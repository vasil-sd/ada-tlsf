package body BitOperations.Extract is

   function Extract (Value : Modular; From, To : Bit_Position) return Modular
   is (Shift.Logic_Right(Value, From) and Mask.Make(To - From + 1));

end BitOperations.Extract;
