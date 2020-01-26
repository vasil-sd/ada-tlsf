module address[exactly Time]

-- моменты времени упорядочены
open util/ordering[Time]

-- адреса и размеры упорядочены
open util/ordering[Addr]
open util/ordering[UniqSize]

-- Реляционная спецификация модели для блоков
-- Адреса - множество уникальных объектов с линейным порядком
-- Размеры - множество уникальных объектов с линейныс порядком
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

-- блок памяти
-- характеризуется адресом
-- и размером
sig Block {
    Address : disj Addr one -> Time,
    Size    : UniqSize one -> Time
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

fun FirstBlock[t:Time] : one Block { {B : Block | B.Address.t = min[Block.Address.t]} }
fun LastBlock[t: Time] : one Block { {B : Block | B.Address.t = max[Block.Address.t]} }

pred Valid[t:Time] {
  -- у всех кроме последнего есть следующий
  all B : Block
  | B != LastBlock[t] implies {
    one Address.t.(Sum[B.Address.t, B.Size.t])
  }
  -- у последнего нет следующего
  no Address.t.(Sum[LastBlock[t].Address.t, LastBlock[t].Size.t])
  -- у первого нет предыдущего
  FirstBlock[t].Address.t not in { 
    A : Addr
    | all B : Block
    | A = Sum[B.Address.t, B.Size.t]
  }
  -- у каждого кроме первого есть предыдущий
  all B : Block - FirstBlock[t]
  | one BPrev : Block - B
  | Sum[BPrev.Address.t, BPrev.Size.t] = B.Address.t
}

-- этот предикат говорит о том, что с T.prev до T поменялись
-- только блоки B_Except, все остальные остались такие же
pred AllBlocksAreSameExcept[T:Time, B_Except:set Block] {
  all B : Block - B_Except {
    B.Address.(T.prev) = B.Address.T
    B.Size.(T.prev) = B.Size.T
  }
}

run { 
  all t : Time | Valid[t]
  one B : Block
  | all T : Time - first
  | AllBlocksAreSameExcept[T, B]
}  for 5 but 10 UniqSize, exactly 4 Block, exactly 8 Time
