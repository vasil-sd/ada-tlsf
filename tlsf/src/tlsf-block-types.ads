with System;
with Interfaces;
with TLSF.Config;

package TLSF.Block.Types with SPARK_Mode, Pure, Preelaborate is

   use TLSF.Config;
   use Interfaces;
   
   type Size is new Natural range 0 .. 2 ** Max_Block_Size_Log2-1
     with Size => Max_Block_Size_Log2;

   type Size_Bits is mod 2**Size'Size;   
   
   type Address is new Size;
   
   type Address_Bits is mod 2**Address'Size;
   
   Address_Null : constant Address := 0;
   
   subtype Valid_Address is Address
     with Predicate => (Valid_Address /= Address_Null);
   
   function To_Size_Bits (S : Size) return Size_Bits
     with
       Global => null,
       Pure_Function,
       Post => Size(To_Size_Bits'Result) = S;

   function To_Address_Bits (A : Address) return Address_Bits
     with 
       Global => null,
       Pure_Function,
       Post => Address(To_Address_Bits'Result) = A;
      
   Align_Mask : constant := (2 ** Align_Size_Log2) - 1;
   Quantum    : constant := Align_Mask + 1;
   
   function Is_Aligned (Val : Size) return Boolean
     with
       Global => null,
       Pure_Function,
       Contract_Cases =>
         ( (Size_Bits(Val) and Align_Mask) = 0 => Is_Aligned'Result = True,
           others                              => Is_Aligned'Result = False);
   
   function Is_Aligned (Val : Address) return Boolean
     with 
       Global => null,
       Pure_Function,
       Contract_Cases =>
         ( (Address_Bits(Val) and Align_Mask) = 0 => Is_Aligned'Result = True,
           others                                 => Is_Aligned'Result = False);
   
   subtype Aligned_Size is Size with
     Predicate => Is_Aligned(Aligned_Size);

   subtype Aligned_Address is Address with
     Predicate => Is_Aligned(Aligned_Address);

   function Round_Size_Up (S : Size) return Aligned_Size
     with 
       Global => null,
       Pure_Function,
       Pre => S <= Size'Last - Align_Mask,
       Post => Is_Aligned(Round_Size_Up'Result);
   
   function Round_Address_Up (A : Address) return Aligned_Address
     with 
       Global => null,
       Pure_Function,
       Pre => A <= Address'Last - Align_Mask,
       Post => Is_Aligned(Round_Address_Up'Result);
   
   function "+" (A: Aligned_Address; S: Aligned_Size) return Aligned_Address
     with 
       Global => null,
       Pure_Function,
       Pre => Integer(A) + Integer(S) in 0 .. Integer(Address'Last),
     Post => 
       Is_Aligned("+"'Result)
       and "+"'Result = Aligned_Address(Integer(A) + Integer(S));

   function "+" (L, R : Aligned_Size) return Aligned_Size
     with 
       Global => null,
       Pure_Function,
       Pre => Integer(L) + Integer(R) in 0 .. Integer(Address'Last),
     Post => 
       Is_Aligned ("+"'Result)
     and "+"'Result = Aligned_Size (Integer (L) + Integer (R));

   -- To is not inclusive, ie [From, To)
   function "-" (To, From : Aligned_Address) return Aligned_Size
     with
       Global => null,
       Pure_Function,
       Pre => To >= From,
       Post => Is_Aligned ("-"'Result)
     and "-"'Result = Aligned_Size (Integer (To) - Integer (From));
     
   
   -- address space for blocks
   type Address_Space is record
      First : Aligned_Address := Quantum;
      Last  : Aligned_Address := Address'Last - (Quantum - 1);
   end record
     with Predicate => 
       First >= Quantum and then
       Last <= Address'Last - (Quantum - 1) and then
     Last > First;
   
   type Status is (Free, Occupied)
     with Size => 1;
   -- Free: block is free
   -- Occupied: block in use
   -- Absent: block is absent (previous of the first
   --         block or next of the last)

   type Free_Blocks_List is
      record
         Prev_Address : Aligned_Address := Address_Null;
         Next_Address : Aligned_Address := Address_Null;
      end record
     with Pack,
     Predicate => ((Prev_Address = 0 and then Next_Address = 0) or else 
                  (Prev_Address /=0 and then Next_Address /= 0));

   type Block_Header (Status : Types.Status := Free) is
      record
         Prev_Block_Address : Aligned_Address := Address_Null;
         Size               : Aligned_Size := 0;
         case Status is
            when Free     => Free_List : Free_Blocks_List;
            when Occupied => null;
         end case;
      end record
     with Pack;

   subtype Block_Header_Occupied is Block_Header(Status => Occupied);
   subtype Block_Header_Free is Block_Header(Status => Free);
   
   pragma Assert ((Size_Bits'(Small_Block_Size) and Align_Mask) = 0);
   
   Block_Header_Size          : constant Size := Small_Block_Size;
                                 -- Size(Block_Header'Max_Size_In_Storage_Elements); 
   Block_Header_Occupied_Size : constant Size := Small_Block_Size;
                                 -- Size(Block_Header_Occupied'Max_Size_In_Storage_Elements);
   Block_Header_Free_Size     : constant Size := Small_Block_Size;
                                 -- Size(Block_Header_Free'Max_Size_In_Storage_Elements);

   Empty_Free_List : constant Free_Blocks_List := 
                       Free_Blocks_List'(Address_Null, Address_Null);
   
   pragma Assert (Small_Block_Size >= Block_Header_Size);
   -- should be >= Block_Header max size in storage elements
   pragma Assert (Block_Header_Free_Size >= Block_Header_Occupied_Size);
   
   -- Predicates
   
   function Is_Free_List_Empty (Free_List : Free_Blocks_List)
                                return Boolean
   is (Free_List = Empty_Free_List);
   
   function Is_Block_Free (Block : Block_Header) return Boolean
     is (Block.Status = Free);

   function Is_Block_Occupied (Block : Block_Header) return Boolean
     is (Block.Status = Occupied);
   
   function Is_Block_Linked_To_Free_List (Block : Block_Header_Free) return Boolean
   is (Block.Free_List.Prev_Address /= Address_Null and then 
       Block.Free_List.Next_Address /= Address_Null)
     with Pre => Is_Block_Free (Block),
     Post => (if not Is_Free_List_Empty (Block.Free_List)
                  then Is_Block_Linked_To_Free_List'Result = True
                    else Is_Block_Linked_To_Free_List'Result = False);
--       Contract_Cases => (not Is_Free_List_Empty(Block.Free_List)
--                          => Is_Block_Linked_To_Free_List'Result = True,
--                          others 
--                          => Is_Block_Linked_To_Free_List'Result = False);
   
   function Is_Block_Last_In_Free_List (Block: Block_Header) return Boolean
   is (Block.Free_List /= Empty_Free_List and then
       Block.Free_List.Prev_Address = Block.Free_List.Next_Address)
     with Pre => Is_Block_Free(Block),
     Post => (if Block.Free_List /= Empty_Free_List and then
            Block.Free_List.Prev_Address = Block.Free_List.Next_Address
                  then Is_Block_Last_In_Free_List'Result = True
                    else Is_Block_Last_In_Free_List'Result = False);
--       Contract_Cases => 
--         (Block.Free_List /= Empty_Free_List and then
--            Block.Free_List.Prev_Address = Block.Free_List.Next_Address
--          => Is_Block_Last_In_Free_List'Result = True,
--          others => Is_Block_Last_In_Free_List'Result = False);
--     
   function Changed_Only_Links_For_Free_List (Block_Old, Block_New : Block_Header) 
                                              return Boolean 
   is
     (Is_Block_Free(Block_Old) and then
      Is_Block_Free(Block_New) and then
      Block_New.Prev_Block_Address = Block_Old.Prev_Block_Address and then
      Block_New.Size = Block_Old.Size);
   
   -- Calculation of levels
   
   type First_Level_Index is new Natural range SL_Index_Count_Log2 .. FL_Index_Max;
   type Second_Level_Index is new Natural range 0 .. SL_Index_Count - 1;

   pragma Assert (Second_Level_Index'Last = 
                  (2 ** Natural(First_Level_Index'First)) - 1);

   type Level_Index is 
      record
         First_Level  : First_Level_Index;
         Second_Level : Second_Level_Index;
      end record;
   
   function Calculate_Levels_Indices
     (S      : Size_Bits)
      return Level_Index
     with
       Pure_Function,
       Pre => S >= Size_Bits(Small_Block_Size);
   
   function Is_Same_Size_Class(S1, S2: Size) return Boolean
     with
       Pre => 
         S1 >= Small_Block_Size and then
         S2 >= Small_Block_Size,
         Contract_Cases => 
           (Calculate_Levels_Indices(Size_Bits(S1)) =
              Calculate_Levels_Indices(Size_Bits(S2)) => 
                Is_Same_Size_Class'Result = True,
            others                                  =>
              Is_Same_Size_Class'Result = False);
      
end TLSF.Block.Types;

