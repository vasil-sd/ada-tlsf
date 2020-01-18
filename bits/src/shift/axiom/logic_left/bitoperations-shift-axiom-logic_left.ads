generic
package BitOperations.Shift.Axiom.Logic_Left
with SPARK_Mode, Pure, Ghost is

   pragma Warnings (GNAT, Off, "postcondition does not check the outcome of calling");

   procedure Equal_Mult_By_Power_2
     (Value : Modular; Amount : Natural)
     with Pre => Amount in 0 .. Modular'Size,
     Post => (BitOperations.Shift.Logic_Left(Value, Amount) 
              = Modular'Mod(Value * (2 ** Amount)));
   
end BitOperations.Shift.Axiom.Logic_Left;
