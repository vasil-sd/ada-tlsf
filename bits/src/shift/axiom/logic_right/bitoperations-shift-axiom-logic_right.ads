generic
package BitOperations.Shift.Axiom.Logic_Right with
SPARK_Mode, Pure, Ghost is

   pragma Warnings (GNAT, Off, "postcondition does not check the outcome of calling");

   procedure Equal_Div_By_Power_2
     (Value : Modular; Amount : Natural)
     with Pre => Amount in 0..Modular'Size,
     Post => Shift.Logic_Right(Value, Amount) = Value / (2 ** Amount);
   
end BitOperations.Shift.Axiom.Logic_Right;
