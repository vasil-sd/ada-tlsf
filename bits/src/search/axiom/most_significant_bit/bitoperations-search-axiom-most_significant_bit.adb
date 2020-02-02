pragma Ada_2012;
package body BitOperations.Search.Axiom.Most_Significant_Bit with SPARK_Mode => Off is

   -----------------------
   -- Result_Is_Correct --
   -----------------------

   procedure Result_Is_Correct (Value : Modular; Index : Bit_Position) is
   null;

   procedure Order_Preservation_Value_To_Index(Value1, Value2 : Modular;
                                               Index1, Index2 : Bit_Position)
   is null;

   procedure Order_Preservation_Index_To_Value(Value1, Value2 : Modular;
                                               Index1, Index2 : Bit_Position)
   is null;

end BitOperations.Search.Axiom.Most_Significant_Bit;
