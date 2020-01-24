package body TLSF.Proof.Util.Vectors with SPARK_Mode is

   ----------
   -- Find --
   ----------

   function Find
     (Container : V.Sequence; E : Element_Type) return Extended_Index_Type
   is
   begin
      if V.Last(Container) >= Index_Type'First then
         for Idx in Index_Type'First..Index_Type(V.Last(Container)) loop
            if (V.Get(Container, Idx) = E) then
               return Idx;
            end if;
            pragma Loop_Invariant
              (not V.Contains(Container, Index_Type'First, Idx, E));
         end loop;
      end if;
      return Extended_Index_Type'First;
   end Find;

   -----------------
   -- Find_Second --
   -----------------

   function Find_Second
     (Container : V.Sequence; E : Element_Type) return Extended_Index_Type
   is
      use Ada.Containers;
      Len : Count_Type renames V.Length(Container);
      First_Idx : constant Extended_Index_Type := Find (Container, E);
   begin
      if Len > 1 and First_Idx in V.First .. Extended_Index_Type'Pred(V.Last(Container)) then
         for Idx in Extended_Index_Type'Succ(First_Idx)..V.Last(Container) loop
            if V.Get(Container, Idx) = E then
               return Idx;
            end if;
         end loop;
      end if;
      return Extended_Index_Type'First;
   end Find_Second;


end TLSF.Proof.Util.Vectors;
