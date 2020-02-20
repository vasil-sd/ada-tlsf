with Ada.Containers;
with Ada.Containers.Functional_Vectors;

with TLSF.Block.Types;
with TLSF.Config; use TLSF.Config;

package TLSF.Proof.Model.Block with SPARK_Mode, Ghost is

   package BT renames TLSF.Block.Types;
   
   type Block is record
      Address : BT.Aligned_Address;
      Prev_Block_Address : BT.Aligned_Address := BT.Address_Null;
      Size    : BT.Aligned_Size;
   end record
     with Predicate => Size >= BT.Quantum and Address >= BT.Quantum and
     (Prev_Block_Address = BT.Address_Null or 
        (Prev_Block_Address >= BT.Quantum and Prev_Block_Address < Address));

   use type BT.Aligned_Address;
   use type BT.Aligned_Size;
      
   use Ada.Containers;
   subtype Index_Type is Positive;
      
   package FV_Pkg is new Ada.Containers.Functional_Vectors
     (Index_Type   => Index_Type,
      Element_Type => Block);
   
   use FV_Pkg;

   use type BT.Address_Space;
   subtype Address_Space is BT.Address_Space;
   
   -- Address space of model is First_Address .. Last_Address - 1,
   -- ie Last_Address is the first one that is out of address space
   type Formal_Model is record
      Blocks     : FV_Pkg.Sequence;
      Mem_Region : Address_Space;
   end record;
      
   function Valid_Block (AS: Address_Space; B: Block) return Boolean
   is (B.Address in AS.First..AS.Last and then
       Integer(B.Address) + Integer(B.Size) in 0..Integer(BT.Address'Last) and then
       B.Address + B.Size in AS.First .. AS.Last and then
         (B.Prev_Block_Address = BT.Address_Null or else
          B.Prev_Block_Address in AS.First .. AS.Last))
     with Post => (if Valid_Block'Result = True 
                     then B.Address in AS.First..AS.Last and
                       B.Address + B.Size in AS.First .. AS.Last and
                     (B.Prev_Block_Address = BT.Address_Null or
                          B.Prev_Block_Address in AS.First .. AS.Last));
   pragma Annotate (GNATprove, Inline_For_Proof, Valid_Block);
     
   function Next_Block_Address (B: Block)
                                return BT.Aligned_Address
   is (B.Address + B.Size)
     with Pre => Integer(B.Address) + Integer(B.Size) in 0..Integer(BT.Address'Last);
   pragma Annotate (GNATprove, Inline_For_Proof, Next_Block_Address);
   
   function Neighbor_Blocks (B_Left, B_Right: Block)
                              return Boolean
   is (Next_Block_Address (B_Left) = B_Right.Address
       and B_Right.Prev_Block_Address = B_Left.Address)
     with Pre => Integer (B_Left.Address) + Integer (B_Left.Size) in 0 .. Integer (BT.Address'Last);     
   pragma Annotate (GNATprove, Inline_For_Proof, Neighbor_Blocks);

   -- excessive, but for clarity
   function Blocks_Addresses_Are_In_Ascending_Order(Bs : FV_Pkg.Sequence;
                                                    From : Index_Type;
                                                    To   : Extended_Index)
                                                    return Boolean
   is (if To >= 1 then
         (for all Idx in From..To-1 =>
             Get(Bs,Idx).Address < Get(Bs, Idx+1).Address))
   with Pre => To <= Last(Bs);
   pragma Annotate (GNATprove, Inline_For_Proof, Blocks_Addresses_Are_In_Ascending_Order);
   
   function All_Blocks_Are_Valid (AS : Address_Space;
                                  BS : FV_Pkg.Sequence;
                                  From : Index_Type;
                                  To   : Extended_Index)
                                  return Boolean
   is (for all Idx in From..To => Valid_Block (AS, Get(BS, Idx)))
     with Pre => To <= Last(BS);
   pragma Annotate (GNATprove, Inline_For_Proof, All_Blocks_Are_Valid);
   
   function Boundary_Blocks_Coverage_Is_Correct(AS: Address_Space;
                                                BS : FV_Pkg.Sequence)
                                                return Boolean
   is (if Last(BS) >=1
       then 
         (Get (BS, 1).Address = AS.First
          and Get (BS, 1).Prev_Block_Address = BT.Address_Null
          and Next_Block_Address(Get(BS, Last(BS))) = AS.Last))
       with 
         Pre => All_Blocks_Are_Valid(AS, BS, 1, Last(BS));
   
   function Coverage_Is_Continuous (AS : Address_Space;
                                    BS : FV_Pkg.Sequence;
                                    From : Index_Type;
                                    To   : Extended_Index)
                                    return Boolean
   is (if To >= 1
       then (for all Idx in From .. To-1
             => Neighbor_Blocks(Get(BS, Idx), Get(BS, Idx+1))))
     with Pre => To <= Last(BS) 
     and then All_Blocks_Are_Valid(AS, BS, From, To);
   pragma Annotate (GNATprove, Inline_For_Proof, Coverage_Is_Continuous);
   
   function Blocks_Overlap (AS: Address_Space; B1, B2: Block) return Boolean
   is (B1.Address in B2.Address..(B2.Address + B2.Size - 1)
       or B1.Address + B1.Size -1 in B2.Address..(B2.Address + B2.Size - 1)
       or B2.Address in B1.Address..(B1.Address + B1.Size - 1)
       or B2.Address + B2.Size -1 in B1.Address..(B1.Address + B1.Size - 1))
   with Pre => Valid_Block(AS, B1) and Valid_Block(AS, B2);
   pragma Annotate (GNATprove, Inline_For_Proof, Blocks_Overlap);
   
   function Blocks_Do_Not_Overlap (AS : Address_Space;
                                   BS : FV_Pkg.Sequence;
                                   From : Index_Type;
                                   To   : Extended_Index)
                                   return Boolean
   is (for all Idx1 in From..To =>
         (for all Idx2 in From..To => 
            (if Idx1 /= Idx2 
             then not Blocks_Overlap(AS, Get(BS, Idx1), Get(BS, Idx2)))))
       with Pre => To <= Last(BS)
       and then All_Blocks_Are_Valid(AS, BS, From, To);
   pragma Annotate (GNATprove, Inline_For_Proof, Blocks_Do_Not_Overlap);
   
   function All_Block_Are_Uniq (AS : Address_Space;
                                BS : FV_Pkg.Sequence;
                                From : Index_Type;
                                To   : Extended_Index)
                                return Boolean
   is (for all Idx1 in From..To => 
         (for all Idx2 in From..To =>
            (if Get (BS, Idx1) = Get (BS, Idx2)
             then Idx1 = Idx2)))
       with Pre => To <= Last(BS)
     and then All_Blocks_Are_Valid(AS, BS, From, To);
   pragma Annotate (GNATprove, Inline_For_Proof, All_Block_Are_Uniq);

   function All_Block_Addresses_Are_Uniq (AS : Address_Space;
                                BS : FV_Pkg.Sequence;
                                From : Index_Type;
                                To   : Extended_Index)
                                return Boolean
   is (for all Idx1 in From..To => 
         (for all Idx2 in From..To =>
            (if Get (BS, Idx1).Address = Get (BS, Idx2).Address
             then Idx1 = Idx2)))
       with Pre => To <= Last(BS)
     and then All_Blocks_Are_Valid(AS, BS, From, To);
   pragma Annotate (GNATprove, Inline_For_Proof, All_Block_Addresses_Are_Uniq);

   
   function Partial_Valid(AS: Address_Space; BS: FV_Pkg.Sequence;
                          From : Index_Type; To : Extended_Index)
                          return Boolean
   is (All_Blocks_Are_Valid(AS, BS, From, To)
       and then Blocks_Addresses_Are_In_Ascending_Order(BS, From, To)
       and then Coverage_Is_Continuous(AS, BS, From, To)
       and then Blocks_Do_Not_Overlap(AS, BS, From, To)
       and then All_Block_Are_Uniq (AS, BS, From, To)
       and then All_Block_Addresses_Are_Uniq (AS, BS, From, To))
     with Global => null,
     Depends => (Partial_Valid'Result => (AS, BS, From, To)),
     Pre => To <= Last(BS),
     Pure_Function;
   
   function Valid(M : Formal_Model) return Boolean
   is (Partial_Valid(M.Mem_Region, M.Blocks, 1, Last(M.Blocks))
       and then Boundary_Blocks_Coverage_Is_Correct(M.Mem_Region, M.Blocks))
     with Global => null,
       Depends => (Valid'Result => M),
     Pure_Function;
   
   procedure Equality_Preserves_Validity (Old_M, New_M : Formal_Model)
     with Global => null,
     Pre => Valid (Old_M) and Old_M = New_M,
     Post => Valid (New_M);
   
   function Address_In_Model (M : Formal_Model; Addr : BT.Aligned_Address)
     return Boolean
   is (for some Idx in 1 .. Last (M.Blocks) =>
          Get (M.Blocks, Idx).Address = Addr)
     with 
       Global => null,
       Pure_Function,
       Pre => Valid (M);
   
   function In_Model (M : Formal_Model; B : Block) return Boolean
   is (Contains (M.Blocks, 1, Last (M.Blocks), B))
     with Global => null,
     Pure_Function,
     Pre => Valid (M),
     Post => (if In_Model'Result then Address_In_Model (M, B.Address));
   
   procedure Addresses_Equality_Implies_Blocks_Equality
     (M : Formal_Model)
     with Global => null,
     Pre => Valid (M),
     Post => (for all I in 1 .. Last (M.Blocks) => In_Model (M, Get (M.Blocks, I)))
     and then
       (for all I in 1 .. Last (M.Blocks) =>
          (for all J in 1 .. Last (M.Blocks) =>
               (if Get (M.Blocks, I).Address = Get (M.Blocks, J).Address
                      then I = J and then 
                        Get (M.Blocks, I) = Get (M.Blocks, J))));

   procedure Addresses_Equality_Implies_Blocks_Equality
     (M           : Formal_Model;
      Left, Right : Block)
     with Global => null,
     Pre => Valid (M) and then In_Model (M, Left) and then In_Model (M, Right),
     Post => (if Left.Address = Right.Address then Left = Right);
   
   function Is_First_Block(M: Formal_Model; B: Block) return Boolean
     with 
       Global => null,
       Pure_Function,
       Pre => Valid (M) and then In_Model (M, B),
     Post => (if B.Address = M.Mem_Region.First
                then B = Get (M.Blocks, 1) and
                  Is_First_Block'Result = True
                    else Is_First_Block'Result = False);
   
   function Is_Last_Block(M: Formal_Model; B: Block) return Boolean
     with
       Global => null,
       Pure_Function,
       Pre => Valid (M) and then In_Model (M, B),
     Post => (if Next_Block_Address (B) = M.Mem_Region.Last
                  then B = Get (M.Blocks, Last (M.Blocks)) and
                Is_Last_Block'Result = True
                  else Is_Last_Block'Result = False);
   
   function Get_Prev(M: Formal_Model; B: Block) return Block
     with
       Global => null,
       Pure_Function,
       Pre => 
         Valid (M)
     and then In_Model (M, B)
     and then not Is_First_Block (M, B),
     Post =>
       Valid_Block (M.Mem_Region, Get_Prev'Result)
     and In_Model (M, Get_Prev'Result)
     and Neighbor_Blocks (Get_Prev'Result, B);
   
   function Get_Next(M: Formal_Model; B: Block) return Block
     with
       Global => null,
       Pure_Function,
       Pre => Valid (M)
     and then In_Model (M, B)
     and then not Is_Last_Block (M, B),
     Post =>
       Valid_Block(M.Mem_Region, Get_Next'Result)
     and In_Model(M, Get_Next'Result)
     and Neighbor_Blocks(B, Get_Next'Result);

   procedure Equality_Preserves_Block_Relations
     (Left_M, Right_M : Formal_Model;
      B               : Block)
     with Global => null,
     Pre => Valid (Left_M) and then Left_M = Right_M
     and then In_Model (Left_M, B),
     Post => Valid (Right_M) and then
     In_Model (Right_M, B) and then
     Is_Last_Block (Left_M, B) = Is_Last_Block (Right_M, B) and then
     Is_First_Block (Left_M, B) = Is_First_Block (Right_M, B) and then
     (if not Is_Last_Block (Left_M, B) then
          Get_Next (Left_M, B) = Get_Next (Right_M, B)) and then
     (if not Is_First_Block (Left_M, B) then
          Get_Prev (Left_M, B) = Get_Prev (Right_M, B));
      
   function Initial_Block (Space : Address_Space)
                           return Block
     with Post =>
       Valid_Block (Space, Initial_Block'Result) and then
     Initial_Block'Result.Address = Space.First and then 
     Next_Block_Address (Initial_Block'Result) = Space.Last and then
     Initial_Block'Result.Prev_Block_Address = BT.Address_Null;
   
   function Init_Model(Space : Address_Space)
                       return Formal_Model
     with 
       Post => Length(Init_Model'Result.Blocks) = 1
     and then Init_Model'Result.Mem_Region = Space
     and then Get (Init_Model'Result.Blocks, 1).Address
     = Init_Model'Result.Mem_Region.First
     and then Next_Block_Address (Get (Init_Model'Result.Blocks, 1))
       = Init_Model'Result.Mem_Region.Last
     and then Get (Init_Model'Result.Blocks, 1) = Initial_Block (Space)
     and then Valid (Init_Model'Result)
     and then In_Model (Init_Model'Result, Initial_Block (Space))
     and then Is_Last_Block (Init_Model'Result, Initial_Block (Space))
     and then Is_First_Block (Init_Model'Result, Initial_Block (Space));
   
   procedure Split_Block (M               : Formal_Model;
                          B               : Block;
                          L_Size, R_Size  : BT.Aligned_Size;
                          B_Left, B_Right : out Block;
                          New_M           : out Formal_Model)
     with 
       Global => null,
       Depends => (New_M => (M, B, L_Size, R_Size),
                   B_Left => (B, L_Size),
                   B_Right => (B, L_Size, R_Size)),
       Pre => 
         (Valid (M)
          and then In_Model (M, B))
         and L_Size >= Small_Block_Size
         and R_Size >= Small_Block_Size
         and B.SIze = L_Size + R_Size,
         Post =>
           (Valid (New_M)
            and not In_Model (New_M, B)
            and In_Model (New_M, B_Left)
            and In_Model (New_M, B_Right)
            and B_Left.Address = B.Address
            and B_Left.Size = L_Size
            and B_Left.Prev_Block_Address = B.Prev_Block_Address
            and B_Right.Address = B.Address + L_Size
            and B_Right.Size = R_Size
 
            and Neighbor_Blocks (B_Left, B_Right)
            and Is_First_Block (M, B) = Is_First_Block (New_M, B_Left)
            and Is_Last_Block (M, B) = Is_Last_Block (New_M, B_Right))
           and then (if not Is_First_Block (M, B)
                               then Get_Prev (M, B) = Get_Prev (New_M, B_Left))
           and then (if not Is_Last_Block (M, B)
                               then Get_Next (M, B).Address = Get_Next (New_M, B_Right).Address
                     and then Get_Next (M, B).Size = Get_Next (New_M, B_Right).Size
                     and then Get_Next (New_M, B_Right).Prev_Block_Address = B_Right.Address
                     and then In_Model (New_M, Get_Next (New_M, B_Right)));
   
end TLSF.Proof.Model.Block;
