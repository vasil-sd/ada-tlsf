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

   type Block is record
      Address : BT.Aligned_Address;
      Header  : BT.Block_Header;
   end record;
   
   function Valid_Block (Ctx   : TC.Context;
                         B     : Block)
                         return Boolean
   is (B.Address in Ctx.Memory.Region.First .. Ctx.Memory.Region.Last and then 
         (B.Header.Prev_Block_Address = BT.Address_Null or else 
            (B.Header.Prev_Block_Address in Ctx.Memory.Region.First .. Ctx.Memory.Region.Last
             and then B.Header.Prev_Block_Address < B.Address))
       and then B.Header.Size in BT.Quantum .. Ctx.Memory.Region.Last - B.Address)
     with Global => null;
      
   function To_Model (Ctx  : TC.Context;
                      B    : Block)
                      return MB.Block
     with 
       Global => null,
       Ghost,
       Pre => Valid_Block (Ctx, B),
     Post =>
       To_Model'Result.Address = B.Address and then
       To_Model'Result.Prev_Block_Address = B.Header.Prev_Block_Address and then
       To_Model'Result.Size = B.Header.Size;
   
   function Next_Block_Address (Ctx : TC.Context; B : Block)
                                return BT.Aligned_Address
   is (B.Address + B.Header.Size)
     with Global => null,
     Pre => Valid_Block (Ctx, B),
     Post => Next_Block_Address'Result =
       MB.Next_Block_Address (To_Model (Ctx, B));

   
   
   function Is_First_Block (Ctx  : TC.Context;
                            B    : Block)
                            return Boolean
     with 
       Global => (Proof_In => MC.State),
     Pre => 
       Valid_Block (Ctx, B) and then
     MC.Has_Model (Ctx) and then 
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, B)),
     Post => Is_First_Block'Result =
       MB.Is_First_Block (MC.Get_Block_Model (Ctx), To_Model (Ctx, B));
   
   function Is_Last_Block (Ctx  : TC.Context;
                           B    : Block)
                           return Boolean
     with 
       Global => (Proof_In => MC.State),
     Pre => 
       Valid_Block(Ctx, B) and then
     MC.Has_Model (Ctx) and then 
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, B)),
     Post => Is_Last_Block'Result =
       MB.Is_Last_Block (MC.Get_Block_Model (Ctx), To_Model (Ctx, B));

   function Neighbor_Blocks (Ctx         : TC.Context;
                             Left, Right : Block)
                             return Boolean
   is (Left.Address + Left.Header.Size = Right.Address and then
       Right.Header.Prev_Block_Address = Left.Address)
     with Pre =>
       Valid_Block (Ctx, Left) and then
     Valid_Block (Ctx, Right) and then
     MC.Has_Model (Ctx) and then
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Left)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Right)),
     Post =>
       Neighbor_Blocks'Result = MB.Neighbor_Blocks
         (To_Model (Ctx, Left),
          To_Model (Ctx, Right));

     
--     procedure Get_Next_Block (Ctx : TC.Context;
--                               Addr : BT.Aligned_Address;
--                               Hdr  : BT.Block_Header;
--                               Next_Addr : out BT.Aligned_Address;
--                               Next_Hdr  : out BT.Block_Header)
--       with Global => (Proof_In => MC.State),
--       Pre => Valid_Block (Ctx, Addr, Hdr) and then
--       MC.Has_Model (Ctx) and then 
--       MB.Valid (MC.Get_Block_Model (Ctx)) and then
--       MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Addr, Hdr)) and then
--       not Is_Last_Block (Ctx, Addr, Hdr),
--       Post => 
     
     
   
   pragma Unevaluated_Use_Of_Old (Allow);
   
   procedure Split_Block (Ctx                   : TC.Context;
                          B                     : Block;
                          Left_Size, Right_Size : BT.Aligned_Size;
                          Left, Right           : out Block)
     with Global => (In_Out => MC.State),
     Pre => Valid_Block (Ctx, B) and then
     Left_Size >= Small_Block_Size and then
     Right_Size >= Small_Block_Size and then 
     Left_Size + Right_Size = B.Header.Size and then
     BT.Is_Block_Free (B.Header) and then
     not BT.Is_Block_Linked_To_Free_List (B.Header) and then
     MC.Has_Model (Ctx) and then
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, B)),
     Post => Valid_Block (Ctx, Left)
     and then Valid_Block (Ctx, Right)
     and then BT.Is_Block_Free (Left.Header)
     and then BT.Is_Block_Free (Right.Header)
     and then not BT.Is_Block_Linked_To_Free_List (Left.Header)
     and then not BT.Is_Block_Linked_To_Free_List (Right.Header)
     and then Neighbor_Blocks (Ctx, Left, Right)
     and then MB.Valid (MC.Get_Block_Model (Ctx))
     and then MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Left))
     and then MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Right))
     and then MB.Neighbor_Blocks (To_Model (Ctx, Left), 
                                  To_Model (Ctx, Right))
     and then (if Is_First_Block (Ctx, B)'Old then
                   Is_First_Block (Ctx, Left) and then
                   MB.Is_First_Block (MC.Get_Block_Model (Ctx), To_Model (Ctx, Left)))
     and then (if Is_Last_Block (Ctx, B)'Old then
                   Is_Last_Block (Ctx, Right) and  then
                   MB.Is_Last_Block (MC.Get_Block_Model (Ctx), To_Model (Ctx, Right)));
     
     
   
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
   procedure Store_Block (Ctx    : TC.Context;
                         B      : Block)
     with Pre => 
       Valid_Block (Ctx, B) and then 
     MC.Has_Model (Ctx) and then
     MB.Valid (MC.Get_Block_Model (Ctx)) and then
     MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, B));
        
end TLSF.Block.Operations;
