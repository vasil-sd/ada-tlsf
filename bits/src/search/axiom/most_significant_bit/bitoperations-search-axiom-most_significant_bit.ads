with Bit_Vectors_Prove;

generic
package BitOperations.Search.Axiom.Most_Significant_Bit with
SPARK_Mode, Pure, Ghost is
   
   procedure Result_Is_Correct(Value : Modular; Index : Bit_Position) 
     with Pre => Value /=0 and then Search.Most_Significant_Bit(Value) = Index,
     Post => Bit_Vectors_Prove.MSB(Interfaces.Unsigned_64(Value)) = Index and then
     Value >= 2 ** Index;
   
   procedure Order_Preservation_Value_To_Index(Value1, Value2 : Modular;
                                               Index1, Index2 : Bit_Position)
     with Pre => Value1 /=0 and then Value2 /= 0 and then
     Value1 >= Value2 and then
     Search.Most_Significant_Bit(Value1) = Index1 and then 
     Search.Most_Significant_Bit(Value2) = Index2,
     Post => Index1 >= Index2; 

   procedure Order_Preservation_Index_To_Value(Value1, Value2 : Modular;
                                               Index1, Index2 : Bit_Position)
     with Pre => Value1 /=0 and then Value2 /= 0 and then
     Index1 >= Index2 and then
     Search.Most_Significant_Bit(Value1) = Index1 and then 
     Search.Most_Significant_Bit(Value2) = Index2,
     Post => Value1 >= Value2; 
   
end BitOperations.Search.Axiom.Most_Significant_Bit;
