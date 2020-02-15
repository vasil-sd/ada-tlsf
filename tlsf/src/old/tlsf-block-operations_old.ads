with System;
with TLSF.Config; use TLSF.Config;
with TLSF.Block.Types; use TLSF.Block.Types;
with TLSF.Block.Proof;

package TLSF.Block.Operations_Old with SPARK_Mode is
   
   package Proof renames TLSF.Block.Proof;
   
   function Get_Block_At_Address(Base : System.Address;
                                 Addr : Aligned_Address)
                                 return Block_Header
     with Pre => (Addr /= Address_Null and then
                    Proof.Block_Present_At_Address(Addr)),
     Post => Get_Block_At_Address'Result = Proof.Block_At_Address(Addr);

   procedure Set_Block_At_Address(Base   : System.Address;
                                  Addr   : Aligned_Address;
                                  Header : Block_Header)
     with Pre => (Addr /= Address_Null and then 
                    not Proof.Block_Present_At_Address(Addr)),
     Post => (Proof.Block_Present_At_Address(Addr) and then
                  Proof.Block_At_Address(Addr) = Header);
   
   procedure Remove_Block_At_Address(Base : System.Address;
                                     Addr : Aligned_Address)
     with Pre => (Addr /= Address_Null and then 
                    Proof.Block_Present_At_Address(Addr)),
       Post => not Proof.Block_Present_At_Address(Addr);
   
   -- Work with free lists  
   
   function Check_Blocks_Linked_Correctly 
     (Block_Left, Block_Right : Block_Header;
      Block_Left_Address, Block_Right_Address : Aligned_Address)
      return Boolean
   is
     (Is_Block_Free(Block_Left) and then 
      Is_Block_Free(Block_Right) and then
      Block_Left.Free_List.Next_Address = Block_Right_Address and then
      Block_Right.Free_List.Prev_Address = Block_Left_Address);
   
   function Check_Free_List_Correctness_After_Unlinking
     (Base : System.Address;
      Block : Block_Header)
      return Boolean
   is
      -- properly linked in free list block cannot have zero links
      -- because free list is circular double linked list
     (Check_Blocks_Linked_Correctly
        (Block_Left          => Get_Block_At_Address(Base, Block.Free_List.Prev_Address),
         Block_Right         => Get_Block_At_Address(Base, Block.Free_List.Next_Address),
         Block_Left_Address  => Block.Free_List.Prev_Address,
         Block_Right_Address => Block.Free_List.Next_Address))
     with Pre =>
       Is_Block_Free(Block) and then
     Proof.Block_Present_At_Address(Block.Free_List.Prev_Address) and then
     Proof.Block_Present_At_Address(Block.Free_List.Next_Address);
   
   function Is_Block_Physically_Present_At_Address_And_In_Free_List_For_Specific_Size
     (Base    : System.Address;
      Address : Aligned_Address;
      Size    : Aligned_Size;
      Block   : Block_Header)
      return Boolean
   is 
     (Is_Block_Free(Block) and then
      Proof.Specific_Block_Present_At_Address(Address, Block) and then
      Is_Block_Linked_To_Free_List(Block) and then
      Proof.Is_Block_In_Free_List_For_Size (Size, Address))
       with Ghost;
   
   procedure Unlink_From_Free_List (Base      : System.Address;
                                    Address   : Aligned_Address;
                                    Block     : in out Block_Header;
                                    Free_List : in out Free_Blocks_List)
     with
       Pre => 
   
   -- TODO: think about storing meta info about Free_Lists,
   -- ie add extra structure for Free_Blocks_List for size
         
   Is_Block_Free(Block) and then
   
   -- Free List is not empty
     not Is_Free_List_Empty(Free_List) and then
         
   -- presence in free lists
     Is_Block_Physically_Present_At_Address_And_In_Free_List_For_Specific_Size
       (Base    => Base,
        Address => Address,
        Size    => Block.Size,
        Block   => Block) and then
     
   -- is neighbors from free list are free blocks to (like inductive case)
   -- left heighbor
     Proof.Block_Present_At_Address(Block.Free_List.Prev_Address) and then
     Is_Block_Physically_Present_At_Address_And_In_Free_List_For_Specific_Size
       (Base    => Base,
        Address => Block.Free_List.Prev_Address,
        Size    => Block.Size,
        Block   => Get_Block_At_Address(Base, Block.Free_List.Prev_Address)) and then
       
   -- right heighbor
     Proof.Block_Present_At_Address(Block.Free_List.Next_Address) and then
     Is_Block_Physically_Present_At_Address_And_In_Free_List_For_Specific_Size
       (Base    => Base,
        Address => Block.Free_List.Next_Address,
        Size    => Block.Size,
        Block   => Get_Block_At_Address(Base, Block.Free_List.Next_Address)) and then
       
   -- Last block is in correct state regarding linking
     (if Is_Block_Last_In_Free_List(Block) then
          (Block.Free_List = Free_List and then
               Block.Free_List.Prev_Address = Block.Free_List.Next_Address and then
                 Block.Free_List.Prev_Address = Address)),
   
     Post =>
       
   -- physycal presence same block (modulo free list links) at same address
     Proof.Specific_Block_Present_At_Address(Address, Block) and then
     
   -- removed from free lists (to do may be : for all free_lists: ... ?)
     not Proof.Is_Block_In_Free_List_For_Size (Block.Size, Address) and then
     not Is_Block_Linked_To_Free_List(Block) and then
     
   -- everything the same, except free list links
     Changed_Only_Links_For_Free_List(Block, Block'Old) and then

   -- check that list in correct state ;
     Check_Free_List_Correctness_After_Unlinking
       (Base                => Base,
        Block               => Block'Old) and then
   
   -- Check correst update of Free_List if it is was last block in it
   
     (if Block'Old.Free_List = Free_List'Old then
        Is_Free_List_Empty(Free_List));
   
--     function Is_Free_Block_Splitable(Block : Block_Header) 
--                                      return Boolean
--       with
--         Pre => 
--           Is_Block_Free(Block) and then
--       Block.Size >= Small_Block_Size * 2,
--         
--       Contract_Cases => 
--         ( Block.Size >= 2*Small_Block_Size
--           => Is_Free_Block_Splitable'Result = True,
--           others                           
--           => Is_Free_Block_Splitable'Result = False);
--     
--     -- NB: we can split only unlinked block
--     -- this approach will be helpful for multithread version,
--     -- because we can unlink fast, using fast lock or even move to lockless
--     -- double-linked-lists
--     procedure Split_Free_Block (Base  : System.Address;
--                                 Addr  : Aligned_Address;
--                                 Block : Block_Header;
--                                 Left_Size, Right_Size : Aligned_Size; 
--                                 Block_Left, Block_Right : out Block_Header)
--       with
--         Pre => 
--           
--     -- physical presence
--       Proof.Specific_Block_Present_At_Address(Addr, Block) and then
--  
--     -- Block already should be unlinked from free lists (TODO: all lists?)
--       not Is_Block_Linked_To_Free_List(Block) and then 
--       not Proof.Is_Block_In_Free_List_For_Size(Block.Size, Addr) and then
--       
--     -- splittable
--       Is_Free_Block_Splitable(Block) and then 
--       
--     -- Sizes preservation
--       Block.Size = Left_Size + Right_Size,
--         
--       Post => 
--       
--     -- physical presence : original block is nowhere
--       not Proof.Specific_Block_Present_At_Address(Addr, Block) and then
--  
--     -- check once again that it is not included into any free lists
--       not Is_Block_Linked_To_Free_List(Block) and then 
--     -- TODO: no free list contains blocks, ie we removed it from everywhere
--       not Proof.Is_Block_In_Free_List_For_Size(Block.Size, Addr) and then
--       
--     -- Correctnes of sizes
--       Block_Left.Size = Left_Size and then
--       Block_Right.Size = Right_Size and then
--       
--     -- Check properties of the Left block:
--       
--     -- check if type is correct
--       Is_Block_Free(Block_Left) and then
--  
--     -- physical presense
--       Proof.Specific_Block_Present_At_Address(Addr, Block_Left) and then
--       
--     -- not yet linked into free lists
--       not Is_Block_Linked_To_Free_List(Block_Left) and then 
--       not Proof.Is_Block_In_Free_List_For_Size(Block_Left.Size, Addr) and then
--       
--       -- TODO: add neighbors check
--       
--     -- The same for the right block
--       Is_Block_Free(Block_Right) and then
--       
--       Proof.Specific_Block_Present_At_Address(Addr + Left_Size, Block_Right) and then
--       
--       not Is_Block_Linked_To_Free_List(Block_Right) and then 
--       not Proof.Is_Block_In_Free_List_For_Size(Block_Right.Size, Addr);
--  
--     
--     procedure Link_To_Free_List_For_Size(Base      : System.Address;
--                                          Addr      : Aligned_Address;
--                                          Block     : in out Block_Header;
--                                          Free_List : in out Free_Blocks_List)
--       with
--         Pre =>
--     -- type check
--       Is_Block_Free(Block) and then
--       
--     -- physical presense 
--       Proof.Specific_Block_Present_At_Address(Addr, Block) and then
--       
--     -- not linked to free lists yet (TODO: all free lists?)
--       not Proof.Is_Block_In_Free_List_For_Size(Block.Size, Addr) and then
--       not Is_Block_Linked_To_Free_List(Block),
--       
--       Post =>
--     -- type check
--       Is_Block_Free(Block) and then
--       
--     -- physical presense 
--       Proof.Specific_Block_Present_At_Address(Addr, Block) and then
--  
--     -- linked to specific free list
--       Is_Block_Linked_To_Free_List(Block) and then
--       Proof.Is_Block_Present_In_Exactly_One_Free_List_For_Size(Block.Size, Addr) and then
--     
--     -- everything the same, except free list links
--       Changed_Only_Links_For_Free_List(Block, Block'Old);
   
end TLSF.Block.Operations_Old;
