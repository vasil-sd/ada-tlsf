module block[exactly Time]

-- моменты времени упорядочены
open util/ordering[Time]

-- адреса и размеры упорядочены
open util/ordering[Addr]
open util/ordering[UniqSize]

-- Реляционная спецификация модели для блоков
-- Адреса - множество уникальных объектов с линейным порядком
-- Размеры - множество уникальных объектов с линейным порядком
-- Операции:
--    для адресной арифметики:
--        адрес + размер = адрес
--    для работы с размерами:
--        размер + размер = размер
-- Блоки памяти - множество уникальных объектов, характеризуются адресом и размером
-- Линейно упорядочены (порядок индуцирован адресами)
-- Закрывают всю память встык, то есть (кроме первого и последнего):
-- адрес предыдущего + его размер = адресу следующего
-- у первого нет предыдущего, у последнего - следующего

-- для динамики операций введём время у размеров и адресов блоков
-- для самих адресов и размеров вводить время не будем (возможно это стоило бы
-- ввести для привычности и наглядности, но это потребует намного больше
-- писанины, а семантически будет эквивалентно текущему варианту)

-- Основные инварианты, которые нужно сохранять, введя операции над блоками
-- 1. Сплошное покрытие блоками памяти, без "дыр", по-умолчению считаем, что
--    работаем с выровненными адресами и размерами и все блоки всегда впритык
-- todo, после введения списков свободных
-- 2. свободный блок может быть только в одном списке свободных
-- 3. нет свободных блоков вне списков свободных
-- 4. в списках свободных только свободные блоки.

let Sum [Left, Right] {
  Left.Add[Right]
}

sig Addr {
  -- тут вводим операцию сложения адреса с размером
  Add: UniqSize -> Addr
}

-- Зададим несколько основных свойств на сложение адресов и размеров
-- (не факт, что они все необходимы для корректной модели, но
--  для привычного восприятия точно нужны :) )

-- Сумма адреса и размера всегда должна быть больше этого адреса
fact {
  all Left : Addr - last
  | all Right : UniqSize 
  | let S = Sum[Left, Right]
  | gt[S, Left] 
}

-- Добавление одинакового размера не должно приводить к разным адресам
fact {
  all A : Addr
  | all S : UniqSize
  | lone Sum[A, S]
}

-- Какой бы размер мы не прибавили к последнему адресу, следующий мы не получим
fact {
  no last.(Addr <: Add)
}

-- добавление одинакового размера к разным блокам должно приводить к разным адресам
fact {
  all A : Addr
  | all S : UniqSize
  | lone Add.A.S  
}

-- добавление разных размеров к адресу должно приводить к разным адресам

fact {
  all disj A1, A2 : Addr
  | lone A1.Add.A2
}

-- Тут уникальные упорядоченные размеры
sig UniqSize {
  -- тут вводим операцию сложения размеров
  Add : UniqSize -> UniqSize
}

-- Тут тоже зададим ограничения на Add, чтобы она выглядела привычнее

-- сложение: сумма всегда больше слагаемых
fact {
  all Left : UniqSize
  | all Right : UniqSize 
  | let S = Sum[Left, Right]
  {
    gt[S, Left]
    gt[S, Right]
  }
}

-- добавление одинакового размера не должно приводить к разным размерам
fact {
  all Left : UniqSize
  | all Right : UniqSize
  | lone Sum[Left, Right]  
}

-- добавление одного и того же размера к разным не должно приводить к одному размеру
fact {
  all Right : UniqSize
  | all Result : UniqSize
  | lone Add.Result.Right
}

-- от перестановки результат не меняется
fact {
  all Left : UniqSize
  | all Right : UniqSize
  | Sum[Left, Right] = Sum[Right, Left]
}

-- ассоциативность
fact {
  all S1 : UniqSize
  | all S2 : UniqSize
  | all S3 : UniqSize
  | Sum[Sum[S1, S2], S3] = Sum[S1, Sum[S2, S3]]
}

-- блок памяти
-- характеризуются адресом и размером
sig Block {
    -- блоков с одинаковыми адресами нет (disj)
    -- хотя может это вынести на проверку валидности?
    Address : disj Addr lone -> Time,
    -- а вот с одинаковыми размерами могут быть
    Size    : UniqSize lone -> Time
}

-- адрес и размер должны быть одновременно
-- или одновременно отсутствовать
fact {
  all T : Time
  | all B : Block
  | (one B.Address.T iff one B.Size.T) or
    (no B.Address.T iff no B.Size.T)
}

-- Расположение блоков в памяти: друг за другом, без перекрытия
-- [ <- Size0 -> ][ <- Size1 -> ][ <- Size2 -> ]
-- ^              ^              ^
-- Addr0          Addr1          Addr2
--                Addr0 + Size0  Addr1 + Size1
--
-- Условие правильности адресов:
-- Кроме первого адреса все остальные являются сложением предыдущего с 
-- некоторым уникальным размером


-- немного полезных вспомогательных функций:

-- UsedBlocks - это блоки, которые используются в заданный момент времени для модели
-- для моделирования операций, когда могут появляться/исчезать блоки памяти
-- нужен пул свободных абстрактных блоков, которые ещё не соответствуют
-- каким-то конкретным блокам
-- абстрактный блок - это блок без адреса и размера
-- соответственно появляется два класса блоков: абстрактные и конкретные
-- UsedBlocks - даём список конкретных блоков на заданный момент времени
fun UsedBlocks [t : Time] : set Block { {B : Block | one B.Address.t} }

-- Дуальная к UsedBlocks
fun UnusedBlocks [t : Time] : set Block { Block - t.UsedBlocks }

-- начальный блок: блок с минимальным адресом на нужный момент времени
fun FirstBlock[t:Time] : one Block { {B : Block | B.Address.t = min[t.UsedBlocks.Address.t]} }

-- конечный - с максимальным адресом на нужный момент времени
fun LastBlock[t: Time] : one Block { {B : Block | B.Address.t = max[t.UsedBlocks.Address.t]} }

-- получить следующий блок для заданного на момент времени t
fun NextBlock[t: Time, b : Block] : Block {
  let NextBlockAddress = Sum[b.Address.t, b.Size.t] -- адрес следующего
     -- получаем отношение Block -> Addr на нужный момент времени
  | let RelBlocksToAddressForTime = Address.t
     -- делаем операцию join справа по NextBlockAddress
     -- и получаем все блоки по этому адресу
  | let AllBlocksAtAddress = RelBlocksToAddressForTime.NextBlockAddress
  | AllBlocksAtAddress -- возвращаем результат
}

-- предыдущий блок у данного на момент времени t
fun PrevBlock[t: Time, b : Block] : Block {
  -- возвращаем множество блоков, адрес у которых равен
  -- сумме адреса текущего с его размером
  {B : Block | Sum[B.Address.t, B.Size.t] = b.Address.t}
}

-- Предикат валидности конкретных блоков на момент времени t
pred Valid[t:Time] {
  -- у всех кроме последнего есть следующий и ровно один
  -- и предыдущий у следующего это текущий блок
  all B : t.UsedBlocks - LastBlock[t]
  | one NextBlock[t, B]
    and PrevBlock[t, NextBlock[t,B]] = B

  -- у последнего нет следующего
  no NextBlock[t, LastBlock[t]]

  -- у первого нет предыдущего
  no PrevBlock[t, FirstBlock[t]]

  -- у каждого кроме первого есть предыдущий
  -- и следующий у предыдущего - это текущий блок
  all B : t.UsedBlocks - FirstBlock[t]
  | one PrevBlock[t, B]
    and NextBlock[t, PrevBlock[t, B]] = B
}

-- этот предикат говорит о том, что с T до T.next поменялись
-- только блоки B_Except, все остальные остались такие же
-- его будем использовать для рамочных гипотез при
-- написании предикатов к операциям над блоками
-- (шаг T -> T.next выбран потому, что потом моделирование
-- операций будет по шагам T -> T.next)
pred AllBlocksAreSameExcept[T:Time, B_Except:set Block] {
  all B : Block - B_Except {
    B.Address.(T.next) = B.Address.T
    B.Size.(T.next) = B.Size.T
  }
}

-- тут простой запуск поиска моделей, чтобы посмотреть,
-- что у нас получается и как работают предикаты
Show_All_Except_One_Are_Unchanged_During_Time:
run { 
  all t : Time | Valid[t]
  one B : Block
  | all T : Time - last
  | AllBlocksAreSameExcept[T, B]
}  for 5 but 5 UniqSize, 5 Addr, exactly 6 Block, exactly 3 Time
