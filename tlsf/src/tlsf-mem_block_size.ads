with TLSF.Config;
use TLSF.Config;

private package TLSF.Mem_Block_Size
with SPARK_Mode is

   type Size is mod 2 ** Max_Block_Size_Log2
     with Size => Max_Block_Size_Log2;

   use type SSE.Storage_Count;
   use type SSE.Integer_Address;

   function Align ( Sz : Size) return Size
     with
       Pre => Sz <= Size'Last - Align_Size,
       Post => Sz <= Align'Result and Align'Result mod Align_Size = 0;

   function Align ( Sz : SSE.Storage_Count ) return Size
     with Pre => Sz <= SSE.Storage_Count (Size'Last - Align_Size),
     Post => (Sz <= SSE.Storage_Count (Align'Result)
              and Align'Result mod Align_Size = 0);

   function Align ( Addr : System.Address) return System.Address
     with
       Pre  => SSE.To_Integer (Addr) <= SSE.Integer_Address'Last - Align_Size,
     Post => (SSE.To_Integer (Addr) <= SSE.To_Integer (Align'Result)
              and SSE.To_Integer (Align'Result) mod Align_Size = 0);

   function Align ( Sc : SSE.Storage_Count) return SSE.Storage_Count
     with
       Pre  => Sc <= SSE.Storage_Count'Last - Align_Size,
       Post => Sc <= Align'Result and Align'Result mod Align_Size = 0;

   function "+" (A : System.Address;
                 B : Size)
                 return System.Address;

   function "-" (A : System.Address;
                 B : Size)
                 return System.Address;

end TLSF.Mem_Block_Size;
