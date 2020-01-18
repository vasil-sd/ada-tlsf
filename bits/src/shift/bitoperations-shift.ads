with BitOperations.Types;

generic
   with package Types is new BitOperations.Types (<>);
package BitOperations.Shift with SPARK_Mode, Pure is

   use Types;

   function Logic_Right (Value : in Modular; Amount : in Natural) return Modular
     with Pure_Function, Global => null,
     Pre => Amount in 0..Modular'Size,
     Post => Logic_Right'Result = Value / (2 ** Amount);

   function Logic_Left (Value : Modular; Amount : Natural) return Modular
     with Pure_Function, Global => null,
     Pre => Amount in 0..Modular'Size,
     Post => Logic_Left'Result = Modular'Mod(Value * (2 ** Amount));

end BitOperations.Shift;
