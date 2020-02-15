with System.Storage_Elements;

package body TLSF.Block.Operations with SPARK_Mode is

   package SSE renames System.Storage_Elements;   
   
   --------------------
   -- Is_First_Block --
   --------------------

   function Is_First_Block
     (Ctx : TC.Context; Addr : BT.Aligned_Address; Hdr : BT.Block_Header)
      return Boolean
   is
   begin
      if Addr = Ctx.Memory.Region.First then
         return True;
      end if;
      return False;
   end Is_First_Block;

   --------------------
   -- Is_Last_Block --
   --------------------

   function Is_Last_Block
     (Ctx : TC.Context; Addr : BT.Aligned_Address; Hdr : BT.Block_Header)
      return Boolean
   is
   begin
      if Addr + Hdr.Size = Ctx.Memory.Region.Last then
         return True;
      end if;
      return False;
   end Is_Last_Block;

   --------------
   -- To_Model --
   --------------

   function To_Model
     (Ctx : TC.Context; Addr : BT.Aligned_Address; Hdr : BT.Block_Header)
      return MB.Block
   is
   begin
      return MB.Block'(Address => Addr,
                       Size    => Hdr.Size);
   end To_Model;

   --------------------------
   -- Set_Block_At_Address --
   --------------------------

   procedure Set_Block_At_Address 
     (Ctx : TC.Context; Addr : BT.Aligned_Address; Header : BT.Block_Header)
     with SPARK_Mode => Off
   is
      use type SSE.Integer_Address;
      
      Block : BT.Block_Header with Address =>
        SSE.To_Address (SSE.To_Integer (Ctx.Memory.Base) + 
                            SSE.Integer_Address (Addr)); 
   begin
      Block := Header;
   end Set_Block_At_Address;
   
   
   -----------------
   -- Split_Block --
   -----------------
   
   procedure Split_Block (Ctx                     : TC.Context;
                          Addr                    : BT.Aligned_Address;
                          Hdr                     : BT.Block_Header_Free;
                          Left_Size, Right_Size   : BT.Aligned_Size;
                          Left_Addr, Right_Addr   : out BT.Aligned_Address;
                          Left_Block, Right_Block : out BT.Block_Header_Free)
   is
      
      use type MB.Block;
      use type MB.Formal_Model;
      
      New_Model       : MB.Formal_Model with Ghost;
      B_Left, B_Right : MB.Block with Ghost;
   begin
      Left_Addr := Addr;
      Right_Addr := Left_Addr + Left_Size;
      Left_Block := BT.Block_Header_Free'(Status             => BT.Free,
                                          Prev_Block_Address => Hdr.Prev_Block_Address,
                                          Size               => Left_Size, 
                                          Free_List          => BT.Empty_Free_List);
      Right_Block := BT.Block_Header_Free'(Status             => BT.Free,
                                           Prev_Block_Address => Left_Addr,
                                           Size               => Right_Size,
                                           Free_List          => BT.Empty_Free_List);
      
      pragma Assert (Valid_Block (Ctx, Left_Addr, Left_Block));
      pragma Assert (Valid_Block (Ctx, Right_Addr, Right_Block));
      
      MB.Split_Block (M       => MC.Get_Block_Model (Ctx),
                      B       => To_Model (Ctx, Addr, Hdr),
                      L_Size  => Left_Size,
                      R_Size  => Right_Size,
                      B_Left  => B_Left,
                      B_Right => B_Right,
                      New_M   => New_Model);
      
      MC.Set_Block_Model (Ctx, New_Model);
      
      -- proof that new blocks have their model counterparts
      pragma Assert (To_Model (Ctx, Left_Addr, Left_Block) = B_Left);
      pragma Assert (To_Model (Ctx, Right_Addr, Right_Block) = B_Right);
      
      pragma Assert (MB.Valid (New_Model));
      pragma Assert (MB.In_Model (New_Model, B_Left));
      pragma Assert (MB.In_Model (New_Model, B_Right));

      pragma Assert (MC.Get_Block_Model (Ctx) = New_Model);
      
      MB.Equality_Preserves_Validity (New_Model, MC.Get_Block_Model (Ctx));
      
      pragma Assert (MB.Valid (MC.Get_Block_Model (Ctx)));
      
      pragma Assert (MB.In_Model (MC.Get_Block_Model (Ctx),
                     To_Model (Ctx, Left_Addr, Left_Block)));

      pragma Assert (MB.In_Model (MC.Get_Block_Model (Ctx),
                     To_Model (Ctx, Right_Addr, Right_Block)));

      Set_Block_At_Address (Ctx, Left_Addr, Left_Block);
      Set_Block_At_Address (Ctx, Right_Addr, Right_Block);
      
   end Split_Block;
end TLSF.Block.Operations;
