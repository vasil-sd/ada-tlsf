pragma Ada_2012;

with Interfaces; use Interfaces;

package body BitOperations.Shift with SPARK_Mode => Off is

   -----------------
   -- Logic_Right --
   -----------------

   function Logic_Right (Value : Modular; Amount : Natural) return Modular  is
     (case Modular'Size is
         when 1 .. 8   => Modular (Shift_Right (Unsigned_8 (Value), Amount)),
         when 9 .. 16  => Modular (Shift_Right (Unsigned_16 (Value), Amount)),
         when 17 .. 32 => Modular (Shift_Right (Unsigned_32 (Value), Amount)),
         when others   => Modular (Shift_Right (Unsigned_64 (Value), Amount)));

   ----------------
   -- Logic_Left --
   ----------------

   function Logic_Left (Value : Modular; Amount : Natural) return Modular is
     (case Modular'Size is
         when 1 .. 8   => Modular'Mod (Shift_Left (Unsigned_8 (Value), Amount)),
         when 9 .. 16  => Modular'Mod (Shift_Left (Unsigned_16 (Value), Amount)),
         when 17 .. 32 => Modular'Mod (Shift_Left (Unsigned_32 (Value), Amount)),
         when others   => Modular'Mod (Shift_Left (Unsigned_64 (Value), Amount)));

end BitOperations.Shift;
