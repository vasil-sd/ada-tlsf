with Interfaces;
with Bits;
--  with Bit_Vectors_Prove;
--  with BitOperations.Search.Axiom;
--  with BitOperations.Search.Axiom.Most_Significant_Bit;
--  with BitOperations.Shift.Axiom;
--  with BitOperations.Shift.Axiom.Logic_Left;
--  with BitOperations.Shift.Axiom.Logic_Right;
with TLSF;
with System.Storage_Elements;
procedure main with SPARK_Mode is

   SA : System.Storage_Elements.Storage_Array(0..16384);
   Pool : TLSF.Pool := TLSF.Init_Pool(SA'Address, SA'Length);
   Sz   : Integer := SA'Length;
--
--     type Modular is mod (2**11);
--
--     package B is new Bits(Modular);
--
--     use Bit_Vectors_Prove;
--     use Interfaces;
--
--     package Axioms is new B.Shifts.Axiom;
--     package Axioms_Logic_Left is new Axioms.Logic_Left;
--     package Axioms_Logic_Right is new Axioms.Logic_Right;
--     package S_Axioms is new B.Search.Axiom;
--     package A_MSB is new S_Axioms.Most_Significant_Bit;
--
--     V : Modular := 1;
--     I : B.Bit_Position;

begin
--     --   Axioms_Logic_Left.Equal_Mult_By_Power_2(V, 3);
--     V := B.Logic_Left(V, 3);
--     pragma Assert( V = 8);
--     V := B.Make_Mask(5);
--     pragma Assert(V = 31);
--     V := B.Logic_Right(V, 3);
--  --   Axioms_Logic_Right.Equal_Div_By_Power_2(V,3);
--     pragma Assert(V = 3);
--     I := B.Most_Significant_Bit(V);
--  --   A_MSB.Result_Is_Correct(V, I);
--     pragma Assert(I = 1);
--  --   pragma Assert ( Nth(Unsigned_64(V), I));
--  --   pragma Assert (MSB(Unsigned_64(V)) = 1);
--  --   pragma Assert (MSB(Unsigned_64(V)) = I);
--  --     Bits_Unsigned.T52.BM.Functions.Shifts.Lemmata.Logic_Right_Lemmas.Lemma1(2,1);
   declare
      type I0_t is new System.Storage_Elements.Storage_Array(0..63);
      type I1_t is new System.Storage_Elements.Storage_Array(0..163);
      type I2_t is new System.Storage_Elements.Storage_Array(0..253);
      I0 : I0_t
        with Import, Address => TLSF.Memory_Allocate(I0_t'Max_Size_In_Storage_Elements, Pool);
      I1 : I1_t
        with Import, Address => TLSF.Memory_Allocate(I1_t'Max_Size_In_Storage_Elements, Pool);
      I2 : I2_t
        with Import, Address => TLSF.Memory_Allocate(I2_t'Max_Size_In_Storage_Elements, Pool);
   begin
      for idx in I0'Range loop
         I0(idx) := System.Storage_Elements.Storage_Element(idx);
      end loop;
      for idx in I1'Range loop
         I1(idx) := System.Storage_Elements.Storage_Element(idx);
      end loop;
      for idx in I2'Range loop
         I2(idx) := System.Storage_Elements.Storage_Element(idx);
      end loop;
      TLSF.Memory_Free(I0'Address, Pool);
      TLSF.Memory_Free(I2'Address, Pool);
      TLSF.Memory_Free(I1'Address, Pool);
   end;
end;
