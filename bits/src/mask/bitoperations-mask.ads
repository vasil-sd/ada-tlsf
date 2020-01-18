with BitOperations.Shift;
with BitOperations.Types;

generic
   with package Types is new BitOperations.Types (<>);
package BitOperations.Mask with 
SPARK_Mode, Pure, Preelaborate is

   package Shift is new BitOperations.Shift(Types);

   use Types;
   use Shift;

   function Make (Size : Mask_Size) return Modular is
     (Logic_Right(Modular'Last, Modular'Size - Size))
       with Pre => Size in 0 .. Modular'Size,
       Post => Make'Result = 2 ** Size -1;

end BitOperations.Mask;
