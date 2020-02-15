with TLSF.Block.Types;
with TLSF.Context;
with TLSF.Proof.Model.Block;

package TLSF.Proof.Model.Context with
SPARK_Mode,
  Ghost,
  Abstract_State => (State)
is

   package BT renames TLSF.Block.Types;
   package TC renames TLSF.Context;
   package MB renames TLSF.Proof.Model.Block;

   use type BT.Address;
   use type BT.Size;
   use type BT.Address_Space;
   use type MB.Formal_Model;
   
   function Has_Model (Context : TC.Context) return Boolean
     with Global => State;
   
   function Get_Block_Model (Context : TC.Context) return MB.Formal_Model
     with Global => State,
     Pre => Has_Model (Context),
     Post => Get_Block_Model'Result.Mem_Region = Context.Memory.Region;
   
   procedure Set_Block_Model (Context      : TC.Context;
                              Blocks_Model : MB.Formal_Model)
     with Global => (In_Out => State),
     Pre => Has_Model (Context),
     Post =>
       Has_Model (Context) and
     Get_Block_Model (Context) = Blocks_Model;
   
   procedure Init_Model (Context : TC.Context)
     with Global => (In_Out => State),
     Post => Has_Model (Context) and then
     Get_Block_Model (Context) = MB.Init_Model (Context.Memory.Region);
   
end TLSF.Proof.Model.Context;
