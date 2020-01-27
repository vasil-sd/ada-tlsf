module freelist[exactly Time]

open util/ordering[Time]

-- открываем модуль блоков и параметризуем его временем
open block[Time]

sig FreeList {
  -- Каждый список соотв одному уникальному размеру
  SizeClass   : disj one UniqSize,
  Blocks      : set Block -> Time
}

-- списки свободных блоков соответствуют 1-к-1
-- уникальным размерам
fact {
  UniqSize in FreeList.SizeClass
}

-- Инварианты:
-- 1. В списках свободных могут быть только конкретные блоки
-- 2. Размеры блоков должны соответствовать размерам списков
-- 3. Типы блоков должны быть правильно установлены
-- 4. Типы должны быть только у используемых (конкретных) блоков

-- типы блоков

enum BlockType {
  Occupied,
  Free
}

-- Тут будем хранить типы для блоков для каждого момента времени
-- тип у блока в определённый момент времени может и отсутствовать,
-- если этот блок неиспользуется (абстрактный)
one sig Types {
  Type : Block -> BlockType -> Time
}

fact {
  all B : Block
  | all T : Time
  | lone B.Type[T]
}

-- получить тип блока на конкретный момент времени 
fun Type [B: Block, T : Time] : BlockType { Types.Type[B].T }

-- все свободные блоки на конкретный момент времени 
fun FreeBlocks [ T: Time ] : set Block { Types.Type.T.Free }

-- списки свободных блоков, в которых присутствует данный
-- блок на конкретный момент времени
fun FreeList [B : Block, T : Time] : set FreeList {
  {FL : FreeList | B in FL.Blocks.T}
}

-- предикат валидности свободных блоков и списков свободных блоков
pred Valid[T : Time] {
  -- у всех используемых (конкретных) блоков установлены типы
  -- и только один тип на блок
  all B : T.UsedBlocks | one B.Type[T]

  -- абстрактные блоки не имеют типа
  all B : T.UnusedBlocks | no B.Type[T]

  -- все свободные блоки в списке свободных
  T.FreeBlocks in FreeList.Blocks.T

  -- все свободные блоки в списках свободных
  FreeList.Blocks.T in T.FreeBlocks

  -- свободные блоки находятся в соответствующих списках свободных
  all B : T.FreeBlocks | B.FreeList[T].SizeClass = B.Size.T
}

-- посмотрим, что получается
run {
  all T : Time | T.this/Valid and T.block/Valid
  some Bs : Block {
    all T : Time - first
    | AllBlocksAreSameExcept[T, Bs]
  }
  some T : Time | some T.FreeBlocks
} for 7
