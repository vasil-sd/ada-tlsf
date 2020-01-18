with Bit_Vectors_Prove;

generic
package BitOperations.Search.Axiom.Most_Significant_Bit with
SPARK_Mode, Pure, Ghost is
   
   procedure Result_Is_Correct(Value : Modular; Index : Bit_Position) 
     with Pre => Value /=0 and then Search.Most_Significant_Bit(Value) = Index,
     Post => Bit_Vectors_Prove.MSB(Interfaces.Unsigned_64(Value)) = Index;
   
end BitOperations.Search.Axiom.Most_Significant_Bit;
