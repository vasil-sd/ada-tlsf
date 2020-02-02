pragma Ada_2012;
with Bits;
with BitOperations.Search.Axiom;
with BitOperations.Search.Axiom.Most_Significant_Bit;

package body TLSF.Block.Types with SPARK_Mode, Pure, Preelaborate is

   package Bits_Size is new Bits(Size_Bits); use Bits_Size;

   function To_Size_Bits (S : Size) return Size_Bits
   is
      Result : constant Size_Bits := Size_Bits(S);
   begin
      pragma Assert (Natural(Size_Bits'Last) = Natural(Size'Last));
      pragma Assert (Natural(S) in 0 .. Natural(Size_Bits'Last));
      pragma Assert (Size(Result) = S);
      return Result;
   end To_Size_Bits;

   function To_Address_Bits (A : Address) return Address_Bits
   is
      Result : constant Address_Bits := Address_Bits(A);
   begin
      pragma Assert (Natural(Address_Bits'Last) = Natural(Address'Last));
      pragma Assert (Natural(A) in 0 .. Natural(Address_Bits'Last));
      pragma Assert (Address(Result) = A);
      return Result;
   end To_Address_Bits;

   generic
      type Value_Type is range <>;
      type Value_Type_Mod is mod <>;
   function Is_Aligned_Generic(Val : Value_Type_Mod) return Boolean
     with Pre => Integer(Value_Type_Mod'First) = Integer(Value_Type'First)
     and then Integer(Value_Type_Mod'Last) = Integer(Value_Type'Last)
     and then Integer(Val) in 0 .. Integer(Value_Type'Last),
     Contract_Cases =>
       ( (Val and Align_Mask) = 0  => Is_Aligned_Generic'Result = True,
         (Val and Align_Mask) /= 0 => Is_Aligned_Generic'Result = False);

   function Is_Aligned_Generic(Val : Value_Type_Mod) return Boolean
   is
      Result : constant Boolean := (Val and Align_Mask) = 0;
   begin
      return Result;
   end Is_Aligned_Generic;

   function Is_Aligned(Val : Size) return Boolean
   is
      function Is_Aligned_Size is new Is_Aligned_Generic(Size, Size_Bits);
   begin
      return Is_Aligned_Size(Size_Bits(Val));
   end Is_Aligned;

   function Is_Aligned(Val : Address) return Boolean
   is
      function Is_Aligned_Addr is new Is_Aligned_Generic(Address, Address_Bits);
   begin
      return Is_Aligned_Addr(Address_Bits(Val));
   end Is_Aligned;

   ----------------
   -- Round_Size --
   ----------------

   generic
      type Value_Type is range <>;
      type Value_Type_Mod is mod <>;
      with function Is_Aligned (Val : Value_Type_Mod) return Boolean;
   function Round_Generic (V : Value_Type) return Value_Type
     with Pre => V <= Value_Type'Last - Align_Mask
     and then Integer(Value_Type_Mod'First) = Integer(Value_Type'First)
     and then Integer(Value_Type_Mod'Last) = Integer(Value_Type'Last)
     and then Integer(V) in 0 .. Integer(Value_Type'Last),
     Post => Is_Aligned(Value_Type_Mod(Round_Generic'Result))
     and then (Value_Type_Mod(Round_Generic'Result) and Align_Mask) = 0;

   function Round_Generic (V : Value_Type) return Value_Type is
      pragma Assert (V <= Value_Type'Last - Align_Mask);
      USize : constant Value_Type_Mod := Value_Type_Mod(V);
      pragma Assert (USize <= Value_Type_Mod(Size'Last - Align_Mask));
      Adj_Size : constant Value_Type_Mod := USize + Align_Mask;
      Masked_Size : constant Value_Type_Mod := Adj_Size and (not Align_Mask);
      pragma Assert (Natural(Value_Type_Mod'Last) = Natural(Value_Type'Last));
      Result_Size : constant Value_Type := Value_Type(Masked_Size);

   begin
      pragma Assert (Is_Aligned(Masked_Size));
      return Result_Size;
   end Round_Generic;

   function Round_Size_Up (S : Size) return Aligned_Size is
      function Is_Aligned_Val is new Is_Aligned_Generic(Size, Size_Bits);
      function Round is new Round_Generic(Size, Size_Bits, Is_Aligned_Val);
   begin
      return Round(S);
   end Round_Size_Up;

   function Round_Address_Up (A : Address) return Aligned_Address is
      function Is_Aligned_Val is new Is_Aligned_Generic(Address, Address_Bits);
      function Round is new Round_Generic(Address, Address_Bits, Is_Aligned_Val);
   begin
      return Round(A);
   end Round_Address_Up;

   function "+" (A: Aligned_Address; S: Aligned_Size) return Aligned_Address
   is
      Addr : constant Natural := Natural(A) + Natural(S);
      pragma Assert (Addr in 0.. Natural(Address'Last));
      -- TODO add lemma:
      -- Aligned + Aligned = Aligned
      -- or more common case: preservation of aligment by +,-,* operations
      pragma Assume (Is_Aligned(Address(Addr)));
      Result : constant Aligned_Address := Address(Addr);
   begin
      return Result;
   end "+";


   function Calculate_Levels_Indices
     (S : Size_Bits)
      return Level_Index
   is
      package Search_Axiom_Pkg is new Bits_Size.Search.Axiom;
      package MSB_Axiom is new Search_Axiom_Pkg.Most_Significant_Bit;

      First_Bit         : constant Bits_Size.Bit_Position :=
                            Bits_Size.Most_Significant_Bit(S);
      Second_Level_Bits : Size_Bits;

      MSB_Small_Block_Size : constant Bits_Size.Bit_Position :=
                               Bits_Size.Most_Significant_Bit(Small_Block_Size)
                               with Ghost;
      Result : Level_Index;
   begin
      MSB_Axiom.Result_Is_Correct(S, First_Bit);
      MSB_Axiom.Result_Is_Correct(Small_Block_Size, MSB_Small_Block_Size);

      MSB_Axiom.Order_Preservation_Value_To_Index
        (Value1 => S,
         Value2 => Small_Block_Size,
         Index1 => First_Bit,
         Index2 => FL_Index_Shift);
      pragma Assert (First_Bit >= FL_Index_Shift);
      Second_Level_Bits := Bits_Size.Extract(S,
                                        First_Bit - SL_Index_Count_Log2,
                                        First_Bit - 1);
      Result.First_Level  := First_Level_Index (First_Bit);
      Result.Second_Level := Second_Level_Index (Second_Level_Bits);
      return Result;
   end Calculate_Levels_Indices;

   function Is_Same_Size_Class(S1, S2: Size) return Boolean
   is (Calculate_Levels_Indices(Size_Bits(S1)) =
         Calculate_Levels_Indices(Size_Bits(S2)));

end TLSF.Block.Types;
