module op_join[Time]

open util/ordering[Time]
open block[Time]
open freelist[Time]

-- этот модуль является модулем-спецификацией на операцию join над блоками

-- помимо предиката самой операции, мы введём предикаты пред и пост-условий, для
-- того чтобы было ближе к коду и легче было бы перекладывать их в код на Ada/Spark


-- общий предикат валидности модели на момент времени T
pred Valid[T : Time] {
  -- все списки свободных валидные
  freelist/Valid[T]

  -- структура памяти валидная
  block/Valid[T]
}

-- предусловие
pred JoinFreeBlocks_Pre[B_Left, B_Right, B : Block,
                       T : Time]
{
  -- B - абстрактный, это результат соединения блоков,
  --     в коде будет out параметром
  -- B_Left, B_Right - конкретные свободные блоки
  -- T момент времени перед соединением блоков

  -- модель валидна
  this/Valid[T]

  -- B_Left и B_Right - в списке свободных
  B_Left + B_Right in T.FreeBlocks

  -- B в списке абстрактных
  B in T.UnusedBlocks
  
  -- B_Left и B_Right - соседние
  NextBlock[T, B_Left] = B_Right
  PrevBlock[T, B_Right] = B_Left
}

-- постусловие
pred JoinFreeBlocks_Post[B_Left, B_Right, B : Block,
                        T_Old, T : Time]
{

  -- B материализовался и есть в списке свободных блоков
  B in T.UsedBlocks
  B in T.FreeBlocks
  
  -- B_Left и B_Right дематериализовались и исчезли
  -- из списков свободных
  B_Left + B_Right not in T.FreeBlocks
  B_Left + B_Right in T.UnusedBlocks 
  
  -- Размер результирующего блока равен сумме размеров
  -- исходных
  B.Size.T = Sum[B_Left.Size.T_Old, B_Right.Size.T_Old]

  -- проверка прежних соседних c B_Left/B_Right по памяти блоков
  PrevBlock[T, B] = PrevBlock[T_Old, B_Left]
  NextBlock[T, B] = NextBlock[T_Old, B_Right]

  this/Valid[T]
}


-- основной предикат объединения
-- свободных блоков
pred JoinFreeBlocks[B_Left, B_Right, B : Block,
                   T : Time]
{
  let NextT = T.next {

    -- Установили адрес и размер новому блоку
    B.Address.NextT = B_Left.Address.T
    B.Size.NextT = Sum[B_Left.Size.T, B_Right.Size.T]

    -- добавили в списки свободных для соответствующих
    -- классов размеров
    B.FreeList[NextT] = FreeListForSizeClass[B.Size.NextT]
    B.Type[NextT] = Free

    -- Удалили старые блоки
    no B_Left.Address.NextT
    no B_Left.Size.NextT

    no B_Right.Address.NextT
    no B_Right.Size.NextT

    -- из списков свободных
    B_Left not in FreeListForSizeClass[B_Left.Size.T].Blocks.NextT
    no B_Left.FreeList[NextT]
    no B_Left.Type[NextT]

    B_Right not in FreeListForSizeClass[B_Right.Size.T].Blocks.NextT
    no B_Right.FreeList[NextT]
    no B_Right.Type[NextT]
  }
}

-- теперь проверим корректность
-- если выполняется предусловие, то можно выполнить Split
-- и должно выполняться постусловие в следующий момент времени
-- и это должно выполняться для всех возможных моделей
Check_SplitFreeBlock:
check {
  all T : Time - last
  | all disj B_Left, B_Right, B : Block
  | {
      JoinFreeBlocks_Pre[B_Left, B_Right, B, T]
      JoinFreeBlocks[B_Left, B_Right, B, T]
      -- далее идут три предиката, так называемые рамочные предикаты
      -- которые задают область динамики, всё остальное считаеся неизменным
      -- во время шага T->T.next
      let ChangingBlocks = B + B_Left + B_Right -- изменяющиеся блоки
      | let ChangingFreeLists = -- изменяющиеся списки свободных блоков
            FreeListForSizeClass[B.Size.(T.next) + B_Left.Size.T + B_Right.Size.T] 
        {
          T.AllBlocksAreSameExcept[ChangingBlocks]
          T.AllFreeListsAreSameExcept[ChangingFreeLists]
          T.AllBlockTypesAreSameExcept[ChangingBlocks]
        }
    }
    implies
     JoinFreeBlocks_Post[B_Left, B_Right, B, T, T.next]
} for 9 but 5 Time
