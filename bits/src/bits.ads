with BitOperations.Types;
with BitOperations.Shift;
with BitOperations.Mask;
with BitOperations.Extract;
with BitOperations.Search;

generic
   type Modular is mod <>;
package Bits with SPARK_Mode, Pure, Preelaborate is

   package Types is new BitOperations.Types(Modular);
   package Shifts is new BitOperations.Shift(Types);
   package Mask is new BitOperations.Mask(Types);
   package Extract_Pkg is new BitOperations.Extract(Types);
   package Search is new BitOperations.Search(Types);

   subtype Bit_Position is Types.Bit_Position;
   subtype Mask_Size is Types.Mask_Size;

   function Logic_Left (Value : Modular; Amount : Natural) return Modular
       renames Shifts.Logic_Left;

   function Logic_Right (Value : Modular; Amount : Natural) return Modular
       renames Shifts.Logic_Right;

   function Make_Mask (Size : Mask_Size) return Modular
       renames Mask.Make;

   function Extract (Value : Modular; From, To: Bit_Position) return Modular
     renames Extract_Pkg.Extract;

   function Most_Significant_Bit (Value : Modular) return Bit_Position
       renames Search.Most_Significant_Bit;

end Bits;
