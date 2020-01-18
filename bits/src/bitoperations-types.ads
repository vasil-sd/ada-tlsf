generic
   type Modular_Type is mod <>;
package BitOperations.Types With
SPARK_Mode, Pure is

   Pragma Assert (Modular_Type'Last = 2 ** Modular_Type'Size - 1);

   subtype Modular is Modular_Type;
   subtype Bit_Position is Natural range 0 .. Modular'Size - 1;
   subtype Mask_Size is Natural range 1 .. Modular'Size;

end BitOperations.Types;
