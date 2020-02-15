with TLSF.Config;
with TLSF.Block.Types;
with TLSF.Context;
with TLSF.Proof.Model.Context;
with TLSF.Proof.Model.Block;

package TLSF.Block.Operations with SPARK_Mode is

   use TLSF.Config;
   
   package BT renames TLSF.Block.Types;
   package TC renames TLSF.Context;
   package MB renames TLSF.Proof.Model.Block;
   package MC renames TLSF.Proof.Model.Context;

   use type BT.Address;
   use type BT.Size;
   
   function Valid_Block (Ctx   : TC.Context;
                         Addr  : BT.Aligned_Address;
                         Hdr   : BT.Block_Header)
                         return Boolean
   is (Addr in Ctx.Memory.Region.First .. Ctx.Memory.Region.Last and then 
       Hdr.Size in BT.Quantum .. Ctx.Memory.Region.Last - Addr)
     with Global => null;
   
   function To_Model (Ctx  : TC.Context;
                      Addr : BT.Aligned_Address;
                      Hdr  : BT.Block_Header)
                      return MB.Block
     with 
       Global => null,
       Ghost,
       Pre => Valid_Block (Ctx, Addr, Hdr),
     Post =>
       To_Model'Result.Address = Addr and then
       To_Model'Result.Size = Hdr.Size;
   
   function Is_First_Block (Ctx  : TC.Context;
                            Addr : BT.Aligned_Address;
                            Hdr  : BT.Block_Header)
                            return Boolean
     with 
       Global => (Proof_In => MC.State),
     Pre => 
       Valid_Block(Ctx, Addr, Hdr) and then
     MC.Has_Model (Ctx) and then 
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Hdr)),
     Post => Is_First_Block'Result =
       MB.Is_First_Block (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Hdr));
   
   function Is_Last_Block (Ctx  : TC.Context;
                           Addr : BT.Aligned_Address;
                           Hdr  : BT.Block_Header)
                           return Boolean
     with 
       Global => (Proof_In => MC.State),
     Pre => 
       Valid_Block(Ctx, Addr, Hdr) and then
     MC.Has_Model (Ctx) and then 
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Hdr)),
     Post => Is_Last_Block'Result =
       MB.Is_Last_Block (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Hdr));

   pragma Unevaluated_Use_Of_Old (Allow);
   
   procedure Split_Block (Ctx                     : TC.Context;
                          Addr                    : BT.Aligned_Address;
                          Hdr                     : BT.Block_Header_Free;
                          Left_Size, Right_Size   : BT.Aligned_Size;
                          Left_Addr, Right_Addr   : out BT.Aligned_Address;
                          Left_Block, Right_Block : out BT.Block_Header_Free)
     with Global => (In_Out => MC.State),
     Pre => Valid_Block (Ctx, Addr, Hdr) and then
     Left_Size >= Small_Block_Size and then
     Right_Size >= Small_Block_Size and then 
     Left_Size + Right_Size = Hdr.Size and then
     not BT.Is_Block_Linked_To_Free_List (Hdr) and then
     MC.Has_Model (Ctx) and then
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Hdr)),
     Post => Valid_Block (Ctx, Left_Addr, Left_Block)
     and then Valid_Block (Ctx, Right_Addr, Right_Block)
     and then not BT.Is_Block_Linked_To_Free_List (Left_Block)
     and then not BT.Is_Block_Linked_To_Free_List (Right_Block)
     and then MB.Valid (MC.Get_Block_Model (Ctx))
     and then MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Left_Addr, Left_Block))
     and then MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Right_Addr, Right_Block))
     and then (if Is_First_Block (Ctx, Addr, Hdr)'Old then
                   Is_First_Block (Ctx, Left_Addr, Left_Block))
     and then (if Is_First_Block (Ctx, Addr, Hdr)'Old then
                   MB.Is_First_Block (MC.Get_Block_Model (Ctx), To_Model (Ctx, Left_Addr, Left_Block)))
     and then (if Is_Last_Block (Ctx, Addr, Hdr)'Old then
                   Is_Last_Block (Ctx, Right_Addr, Right_Block))
     and then (if Is_Last_Block (Ctx, Addr, Hdr)'Old then
                   MB.Is_Last_Block (MC.Get_Block_Model (Ctx), To_Model (Ctx, Right_Addr, Right_Block)));
     
     
   
--     function Get_Prev_Free_Block (Ctx  : TC.Context;
--                                   Addr : BT.Aligned_Address;
--                                   Hdr  : BT.Block_Header_Free)
--                                   return BT.Block_Header_Free
--       with
--         Global => null,
--         Pure_Function,
--         Pre =>
--           BT.Is_Block_Linked_To_Free_List (Hdr) and then
--       MB.Valid (MC.Get_Block_Model (Ctx)) and then
--       In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Hdr)),
--       Post => MB.Valid (MC.Get_Block_Model (Ctx)) and then
--       In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Get_Prev_Free_Block'Result));
--  
--     function Get_Next_Free_Block (Ctx  : TC.Context;
--                                   Addr : BT.Aligned_Address;
--                                   Hdr  : BT.Block_Header_Free)
--                                   return BT.Block_Header_Free
--       with
--         Global => null,
--         Pure_Function,
--         Pre =>
--           BT.Is_Block_Linked_To_Free_List (Hdr) and then
--       MB.Valid (MC.Get_Block_Model (Ctx)) and then
--       In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Hdr)),
--       Post => MB.Valid (MC.Get_Block_Model (Ctx)) and then
--       In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Get_Next_Free_Block'Result));
--  
--     
--     
private
--  
--     function Get_Block_At_Address (Ctx  : TC.Context;
--                                    Addr : Aligned_Address)
--                                    return Block_Header
--       with
--         Global => null,
--         Pure_Function,
--         Pre => 
--           Addr >= BT.Quantum and then 
--           MB.Valid (MC.Get_Block_Model (Ctx)),
--           Post =>
--             MB.Valid (MC.Get_Block_Model (Ctx)) and then
--             MB.In_Model (MC.Get_Block_Model (Ctx),
--                          To_Model (Ctx, Addr, Get_Block_At_Address'Result));
--  
   procedure Set_Block_At_Address (Ctx    : TC.Context;
                                   Addr   : BT.Aligned_Address;
                                   Header : BT.Block_Header)
     with Pre => 
       Valid_Block (Ctx, Addr, Header) and then 
     MC.Has_Model (Ctx) and then
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Header));
        
end TLSF.Block.Operations;
