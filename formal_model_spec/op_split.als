module op_split[Time]

open util/ordering[Time]
open block[Time]
open freelist[Time]

-- этот модуль является модулем-спецификацией на операцию split над блоками

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
pred SplitFreeBlock_Pre[B: Block, B_Left, B_Right : Block,
                        SizeLeft, SizeRight : UniqSize,
                        T : Time]
{
  -- B - свободный
  -- B_Left, B_Right - абстрактные (в коде будут out параметрами)
  -- SizeLeft, SizeRight - размеры новых блоков
  -- T момент времени перед разделением

  -- модель валидна
  this/Valid[T]

  -- B в списке свободных
  B in T.FreeBlocks
  
  -- B_Left и B_Right - абстрактные
  B_Left + B_Right in T.UnusedBlocks

  -- размер старого блока равен сумме новых
  B.Size.T = Sum[SizeLeft, SizeRight]
}

-- постусловие
pred SplitFreeBlock_Post[B: Block, B_Left, B_Right : Block,
                        SizeLeft, SizeRight : UniqSize,
                        T_Old, T : Time]
{

  B in T.UnusedBlocks
  B not in T.FreeBlocks -- избыточно, но для понимания думаю нужно
  
  B_Left + B_Right in T.FreeBlocks

  B_Left + B_Right in T.UsedBlocks -- T.FreeBlocks неявно это подразумевает, но
                                   -- для ясности понимания думаю нужно
  
  B_Left.Size.T = SizeLeft
  B_Right.Size.T = SizeRight

  B.Size.T_Old = Sum[B_Left.Size.T, B_Right.Size.T] -- избыточно, но для ясности

  -- проверяем, что они идут встык в памяти
  B_Right = NextBlock[T, B_Left]
  B_Left = PrevBlock[T, B_Right]

  -- проверка прежних соседних c B по памяти блоков
  PrevBlock[T_Old, B] = PrevBlock[T, B_Left]
  NextBlock[T_Old, B] = NextBlock[T, B_Right]

  this/Valid[T]
}


-- само разбиение свободного блока
pred SplitFreeBlock[B: Block,
                    B_Left, B_Right : Block,
                    SizeLeft, SizeRight : UniqSize,
                    T : Time]
{
  let NextT = T.next {

    -- установили адрес и размер
    B_Left.Address.NextT = B.Address.T
    B_Left.Size.NextT = SizeLeft

    B_Right.Address.NextT = Sum[B.Address.T, SizeLeft]
    B_Right.Size.NextT = SizeRight
    
    -- добавили в списки свободных для соответствующих
    -- классов размеров
    B_Left.FreeList[NextT] = FreeListForSizeClass[B_Left.Size.NextT]
    B_Left.Type[NextT] = Free

    B_Right.FreeList[NextT] = FreeListForSizeClass[B_Right.Size.NextT]
    B_Right.Type[NextT] = Free

    -- старый блок удалили из списков свободных
    B not in FreeListForSizeClass[B.Size.T].Blocks.NextT
    no B.FreeList[NextT]
    no B.Type[NextT]

    -- очистили адрес и размер
    -- таким образом переведя его в абстрактные
    no B.Address.NextT
    no B.Size.NextT
  }
}

-- теперь проверим корректность
-- если выполняется предусловие, то можно выполнить Split
-- и должно выполняться постусловие в следующий момент времени
-- и это должно выполняться для всех возможных моделей
Check_SplitFreeBlock:
check {
  all T : Time - last
  | all disj B, B_Left, B_Right : Block
  | all S_Left, S_Right : UniqSize
  | {
      SplitFreeBlock_Pre[B, B_Left, B_Right, S_Left, S_Right, T]
      SplitFreeBlock[B, B_Left, B_Right, S_Left, S_Right, T]
      -- далее идут три предиката, так называемые рамочные предикаты
      -- которые задают область динамики, всё остальное считаеся неизменным
      -- во время шага T->T.next
      let ChangingBlocks = B + B_Left + B_Right -- изменяющиеся блоки
      | let ChangingFreeLists = -- изменяющиеся списки свободных блоков
            FreeListForSizeClass[B.Size.T + S_Left + S_Right] 
        {
          T.AllBlocksAreSameExcept[ChangingBlocks]
          T.AllFreeListsAreSameExcept[ChangingFreeLists]
          T.AllBlockTypesAreSameExcept[ChangingBlocks]
        }
    }
    implies
     SplitFreeBlock_Post[B, B_Left, B_Right, S_Left, S_Right, T, T.next]
} for 9 but 5 Time
