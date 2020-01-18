with BitOperations.Types;
with BitOperations.Shift;
with BitOperations.Mask;
with Interfaces;

generic
   with package Types is new BitOperations.Types (<>);
package BitOperations.Search with SPARK_Mode, Pure, Preelaborate is

   use Types;
   
   package Shift is new BitOperations.Shift(Types);
   package Mask is new BitOperations.Mask(Types);
   
   use Shift;
   
   function Most_Significant_Bit(Value : Modular) return Bit_Position
     with Pure_Function, Global => null,
     Pre => Value /= 0;

end BitOperations.Search;
