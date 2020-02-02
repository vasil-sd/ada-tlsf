with Ada.Containers.Functional_Vectors;

generic
   type Element_Type is range <>;
   with package V is new Ada.Containers.Functional_Vectors
     (Element_Type => Element_Type,
      others => <>);
package TLSF.Proof.Util.Vectors with SPARK_Mode is
   
   use Ada.Containers;
   use type V.Sequence;
   
   subtype Extended_Index_Type is V.Extended_Index;
   subtype Index_Type is V.Index_Type;
   
   use type Extended_Index_Type;
   use type Index_Type;
   use type Element_Type;
   
   function Find (Container : V.Sequence;
                  E         : Element_Type)
                  return Extended_Index_Type
     with 
       Global => null,
       Post =>
         (if Find'Result > Extended_Index_Type'First
              then
                (V.Contains(Container, Find'Result, Find'Result, E)
                 and Find'Result <= V.Last (Container)
                 and E = V.Get (Container, Find'Result))
                  else
              (not V.Contains(Container, Index_Type'First, V.Last(Container), E)));
   
   function Find_Second (Container : V.Sequence;
                         E         : Element_Type)
                         return Extended_Index_Type
     with
       Global => null,
       Post =>
         ( if Find_Second'Result > Extended_Index_Type'First then
             Find_Second'Result <= V.Last (Container)
           and Find(Container, E) > Extended_Index_Type'First
           and Find(Container, E) < Find_Second'Result
           and Find_Second'Result > Index_Type'First
           and E = V.Get (Container, Find(Container, E))
           and E = V.Get (Container, Find_Second'Result));
   
   function At_Least_One (Container : V.Sequence;
                          E         : Element_Type)
                          return Boolean
   is (Find(Container, E) > Extended_Index_Type'First);
   
   function Exactly_One (Container : V.Sequence;
                         E         : Element_Type)
                         return Boolean
   is (Find(Container, E) > Extended_Index_Type'First
       and Find_Second(Container, E) = Extended_Index_Type'First);
   
   function At_Most_One (Container : V.Sequence;
                         E         : Element_Type)
                         return Boolean
   is (Find_Second(Container, E) = Extended_Index_Type'First);
 
end TLSF.Proof.Util.Vectors;
