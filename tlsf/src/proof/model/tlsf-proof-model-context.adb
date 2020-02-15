with System.Storage_Elements;
with Ada.Containers.Formal_Hashed_Maps;

package body TLSF.Proof.Model.Context With
SPARK_Mode,
  Refined_State => (State => Block_Models)
is

   package SSE renames System.Storage_Elements;

   package AC renames Ada.Containers;

   function Hash (Addr : System.Address) return AC.Hash_Type;

   package Map_Pkg is new Ada.Containers.Formal_Hashed_Maps
     (Key_Type        => System.Address,
      Element_Type    => MB.Formal_Model,
      Hash            => Hash);

   Block_Models : Map_Pkg.Map (Capacity => 1000, Modulus => 777);

   function Hash (Addr : System.Address) return AC.Hash_Type
   is
   begin
      return AC.Hash_Type (SSE.To_Integer (Addr));
   end Hash;

   ---------------
   -- Has_Model --
   ---------------

   function Has_Model (Context : TC.Context) return Boolean
     with Refined_Post => Has_Model'Result =
       Map_Pkg.Contains (Block_Models, Context.Memory.Base)
   is
   begin
      return Map_Pkg.Contains (Block_Models, Context.Memory.Base);
   end Has_Model;

   ---------------------
   -- Get_Block_Model --
   ---------------------

   function Get_Block_Model (Context : TC.Context) return MB.Formal_Model
   is
      Model : MB.Formal_Model renames
                Map_Pkg.Element (Block_Models, Context.Memory.Base);
   begin
      -- we cannot guarantee connection of Context and Formal model
      -- tha is why we Assume it :(
      -- TODO: think about this issue
      pragma Assume (Model.Mem_Region = Context.Memory.Region);
      return Model;
   end Get_Block_Model;

   ---------------------
   -- Set_Block_Model --
   ---------------------

   procedure Set_Block_Model
     (Context      : TC.Context;
      Blocks_Model : MB.Formal_Model)
   is
   begin
      Map_Pkg.Replace (Block_Models, Context.Memory.Base, Blocks_Model);
      pragma Assert (Get_Block_Model (Context) = Blocks_Model);
   end Set_Block_Model;

   ----------------
   -- Init_Model --
   ----------------

   procedure Init_Model (Context : TC.Context) is
      Model : MB.Formal_Model := MB.Init_Model (Context.Memory.Region);
      use type Ada.Containers.Count_Type;
   begin
      pragma Assume (Map_Pkg.Length(Block_Models) < Block_Models.Capacity);
      Map_Pkg.Include (Block_Models, Context.Memory.Base, Model);
      pragma Assert (Get_Block_Model (Context) = Model);
   end Init_Model;

end TLSF.Proof.Model.Context;
