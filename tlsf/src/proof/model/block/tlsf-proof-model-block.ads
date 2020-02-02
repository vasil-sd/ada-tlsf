with Ada.Containers;
with Ada.Containers.Functional_Vectors;

with TLSF.Block.Types;
with TLSF.Config; use TLSF.Config;

package TLSF.Proof.Model.Block with SPARK_Mode is

   package BT renames TLSF.Block.Types;
   
   type Block is record
      Address : BT.Aligned_Address;
      Size    : BT.Aligned_Size;
   end record
   with Predicate => Size >= BT.Quantum and Address >= BT.Quantum;

   use type BT.Aligned_Address;
   use type BT.Aligned_Size;
   
   function "=" (Left, Right : Block) return Boolean
   is (Left.Address = Right.Address and then 
       Left.Size = Right.Size)
     with Global => null, Pure_Function;
   
   use Ada.Containers;
   subtype Index_Type is Positive;
      
   package FV_Pkg is new Ada.Containers.Functional_Vectors
     (Index_Type   => Index_Type,
      Element_Type => Block);
   
   use FV_Pkg;
   
   -- Address space of model is First_Address .. Last_Address - 1,
   -- ie Last_Address is the first one that is out of address space
   type Formal_Model is record
      Blocks        : FV_Pkg.Sequence;
      First_Address : BT.Aligned_Address := BT.Quantum;
      Last_Address  : BT.Aligned_Address := BT.Address'Last - (BT.Quantum - 1);
   end record
     with Predicate => 
       First_Address >= BT.Quantum and then
       Last_Address <= BT.Address'Last - (BT.Quantum - 1) and then
     Last_Address > First_Address;
      
   function Valid_Block (M: Formal_Model; B: Block) return Boolean
   is (B.Address in M.First_Address..M.Last_Address and then
       Integer(B.Address) + Integer(B.Size) in 0..Integer(BT.Address'Last) and then
       B.Address + B.Size in M.First_Address..M.Last_Address)
     with Post => (if Valid_Block'Result = True 
                     then B.Address in M.First_Address..M.Last_Address and
                       B.Address + B.Size in M.First_Address..M.Last_Address);
   pragma Annotate (GNATprove, Inline_For_Proof, Valid_Block);
     
   function Next_Block_Address (B: Block)
                                return BT.Aligned_Address
   is (B.Address + B.Size)
     with Pre => Integer(B.Address) + Integer(B.Size) in 0..Integer(BT.Address'Last);
   pragma Annotate (GNATprove, Inline_For_Proof, Next_Block_Address);
   
   function Neighbor_Blocks (B_Left, B_Right: Block)
                              return Boolean
   is (Next_Block_Address(B_Left) = B_Right.Address)
     with Pre => Integer(B_Left.Address) + Integer(B_Left.Size) in 0..Integer(BT.Address'Last);     
   pragma Annotate (GNATprove, Inline_For_Proof, Neighbor_Blocks);

   -- excessive, but for clarity
   function Blocks_Addresses_Are_In_Ascending_Order(M: Formal_Model)
                                                    return Boolean
   is (if Last(M.Blocks) >=2 then
         (for all Idx in 1..Last(M.Blocks)-1 =>
               Get(M.Blocks,Idx).Address < Get(M.Blocks, Idx+1).Address));
   pragma Annotate (GNATprove, Inline_For_Proof, Blocks_Addresses_Are_In_Ascending_Order);
   
   function All_Blocks_Are_Valid (M: Formal_Model)
                                  return Boolean
   is (for all B of M.Blocks => Valid_Block (M, B));
   pragma Annotate (GNATprove, Inline_For_Proof, All_Blocks_Are_Valid);
   
   function Coverage_Is_Continuous (M: Formal_Model)
                                    return Boolean
   is ((if Last(M.Blocks) >=1
        then 
          (Get(M.Blocks, 1).Address = M.First_Address
           and Next_Block_Address(Get(M.Blocks, Last(M.Blocks))) = M.Last_Address))
       and then
         (if Last(M.Blocks) > 1
          then (for all Idx in 1 .. Last(M.Blocks)-1
                => Neighbor_Blocks(Get(M.Blocks, Idx), Get(M.Blocks, Idx+1)))))
   with Pre=> All_Blocks_Are_Valid(M);
   pragma Annotate (GNATprove, Inline_For_Proof, Coverage_Is_Continuous);
   
   function Valid(M : Formal_Model) return Boolean
     with Global => null,
     Pure_Function,
     Contract_Cases =>
       ((All_Blocks_Are_Valid(M)
        and then Blocks_Addresses_Are_In_Ascending_Order(M)
        and then Coverage_Is_Continuous(M))
        => Valid'Result = True,
        
        others => Valid'Result = False);      
         
   function In_Model(M: Formal_Model; B : Block)
                     return Boolean
     with Global => null,
     Pure_Function,
     Contract_Cases =>
       ( Contains(M.Blocks, 1, Last(M.Blocks), B) => In_Model'Result = True,
         others                                    => In_Model'Result = False);
     
   function Init_Model(First_Address: BT.Aligned_Address;
                       Size         : BT.Aligned_Size)
                       return Formal_Model
     with
       Pre => Integer(First_Address) + Integer(Size) in 0 .. Integer(BT.Address'Last) - Integer(BT.Quantum) + 1
     and Size >= Small_Block_Size
     and First_Address >= BT.Quantum, 
       Post => Length(Init_Model'Result.Blocks) = 1
     and Init_Model'Result.First_Address = First_Address
     and Init_Model'Result.Last_Address = First_Address + Size
     and Get(Init_Model'Result.Blocks, 1).Address = First_Address
     and Get(Init_Model'Result.Blocks, 1).Size = Size
     and Next_Block_Address(Get(Init_Model'Result.Blocks, 1))
       = Init_Model'Result.Last_Address
     and In_Model(Init_Model'Result, Block'(First_Address, Size))
     and Valid(Init_Model'Result);
   
   function Is_First_Block(M: Formal_Model; B: Block) return Boolean
     with 
       Global => null,
       Pure_Function,
       Contract_Cases => 
         (Length(M.Blocks) > 0 and then B = Get(M.Blocks, 1) => Is_First_Block'Result = True,
          others                                             => Is_First_Block'Result = False);
   
   function Is_Last_Block(M: Formal_Model; B: Block) return Boolean
     with
       Global => null,
       Pure_Function,
       Contract_Cases =>
         (Length(M.Blocks) > 0 and then B = Get(M.Blocks, Last(M.Blocks))
          => Is_Last_Block'Result = True,
          others => Is_Last_Block'Result = False);

   function Get_Prev(M: Formal_Model; B: Block) return Block
     with
       Global => null,
       Pure_Function,
       Pre => Valid(M)
     and Length(M.Blocks) > 0
     and not Is_First_Block(M, B)
     and In_Model(M, B),
     Post =>
       Valid_Block(M, Get_Prev'Result)
     and In_Model(M, Get_Prev'Result)
     and Neighbor_Blocks(Get_Prev'Result, B);
   
   function Get_Next(M: Formal_Model; B: Block) return Block
     with
       Global => null,
       Pure_Function,
       Pre => Valid(M)
     and Length (M.Blocks) > 0
     and not Is_Last_Block(M, B)
     and In_Model(M, B),
     Post =>
       Valid_Block(M, Get_Next'Result)
     and In_Model(M, Get_Next'Result)
     and Neighbor_Blocks(B, Get_Next'Result);
   
--     function Split_Block(M : Formal_Model;
--                          B : Block;
--                          L_Size, R_Size : BT.Aligned_Size;
--                          B_Left, B_Right : out Block)
--                          return Formal_Model
--       with 
--         Global => null,
--         Pure_Function,
--         Pre => 
--           Valid(M)
--       and In_Model(M, B)
--       and B.SIze = L_Size + R_Size,
--       Post => 
   
end TLSF.Proof.Model.Block;
