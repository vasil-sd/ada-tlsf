pragma Ada_2012;
package body BitOperations.Search with SPARK_Mode, Pure is

   --------------------------
   -- Most_Significant_Bit --
   --------------------------

   function Most_Significant_Bit (Value : Modular) return Bit_Position is
   begin
      for Idx in reverse Bit_Position'First .. Bit_Position'Last loop
         if (Value and Logic_Left(1, Idx)) /= 0 then
            return Idx;
         end if;
      end loop;
      return Bit_Position'First;
   end Most_Significant_Bit;

end BitOperations.Search;
