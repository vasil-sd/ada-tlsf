with BitOperations.Types;
with BitOperations.Shift;
with BitOperations.Mask;

generic
   with package Types is new BitOperations.Types (<>);
package BitOperations.Extract with
SPARK_Mode, Pure, Preelaborate is

   package Shift is new BitOperations.Shift(Types);
   package Mask is new BitOperations.Mask(Types);
   
   use Types;
   
   function Extract (Value : Modular; From, To : Bit_Position) return Modular
     with Pre => To >= From,
     Post => Extract'Result = 
       (Shift.Logic_Right(Value, From) and Mask.Make(To - From + 1));

end BitOperations.Extract;
