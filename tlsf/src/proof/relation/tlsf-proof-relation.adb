pragma Ada_2012;
package body TLSF.Proof.Relation is

   function Relate(Container : R;
                   From, To  : Element_Type)
                   return R
   is
      Len : constant Count_Type := Length(Container);
      A : constant Arrow := (From, To);
   begin
      if Contains(Container, A) then
         return Container;
      else
         pragma Assert (not Contains(Container, A));
         declare
            New_Container : constant R := Add(Container, A);
            New_Len : constant Count_Type := Length(New_Container);
         begin
            pragma Assert (Contains(Container => Container,
                                    Item      => A));
            pragma Assert (New_Len > Len);
            return New_Container;
         end;
      end if;
   end Relate;

end TLSF.Proof.Relation;
