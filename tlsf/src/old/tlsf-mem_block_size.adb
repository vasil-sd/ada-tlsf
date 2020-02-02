with TLSF.Config;
use TLSF.Config;

package body TLSF.Mem_Block_Size
with SPARK_Mode is

   generic
      type Modular is mod <>;
      Alignment_Log2: Positive;
   function Align_generic ( V : Modular ) return Modular
     with
       Pre  => V <= Modular'Last - (2 ** Alignment_Log2 - 1),
       Post => (V <= Align_generic'Result and
                  Align_generic'Result mod 2 ** Alignment_Log2 = 0);

   function Align_generic ( V : Modular ) return Modular
   is ((V + (2 ** Alignment_Log2 - 1))
       and not (2 ** Alignment_Log2 - 1));

   function Align ( Sz : Size) return Size is
      function Align is new Align_generic (Size, Align_Size_Log2);
   begin
      return Align (Sz);
   end Align;

   function Align ( Sz : SSE.Storage_Count ) return Size
     is (Align(Size(Sz)));

   function Align ( Addr : System.Address ) return System.Address
   is
      function Align is new Align_generic (SSE.Integer_Address, Align_Size_Log2);
      Int_Addr : SSE.Integer_Address := SSE.To_Integer (Addr);
      Aligned  : SSE.Integer_Address := Align (Int_Addr);
      Result   : System.Address := SSE.To_Address (Aligned);
   begin
      pragma Assert (Int_Addr <= Aligned);
      pragma Assume (SSE.To_Integer(SSE.To_Address(Aligned)) = Aligned);
      pragma Assert (SSE.To_Integer(Addr) <= SSE.To_Integer(Result));
      return Result;
   end Align;

   function Align ( Sc : SSE.Storage_Count ) return SSE.Storage_Count
   is
      type Storage_Count_Mod is mod 2 ** SSE.Storage_Count'Size;
      function Align is new Align_generic (Storage_Count_Mod, Align_Size_Log2);
   begin
      return SSE.Storage_Count (Align (Storage_Count_Mod (Sc)));
   end Align;

   use type SSE.Storage_Offset;

   function "+" (A : System.Address;
                 B : Size)
                 return System.Address
   is (A + SSE.Storage_Offset (B));

   function "-" (A : System.Address;
                 B : Size)
                 return System.Address
   is (A - SSE.Storage_Offset (B));

end TLSF.Mem_Block_Size;
