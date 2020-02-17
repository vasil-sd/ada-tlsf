with System.Storage_Elements;

package body TLSF.Block.Operations with SPARK_Mode is

   package SSE renames System.Storage_Elements;   
   
   --------------------
   -- Is_First_Block --
   --------------------

   function Is_First_Block
     (Ctx : TC.Context; B : Block)
      return Boolean
   is
   begin
      if B.Address = Ctx.Memory.Region.First then
         return True;
      end if;
      return False;
   end Is_First_Block;

   --------------------
   -- Is_Last_Block --
   --------------------

   function Is_Last_Block
     (Ctx : TC.Context; B : Block)
      return Boolean
   is
   begin
      if B.Address + B.Header.Size = Ctx.Memory.Region.Last then
         return True;
      end if;
      return False;
   end Is_Last_Block;

   --------------
   -- To_Model --
   --------------

   function To_Model
     (Ctx : TC.Context; B : Block)
      return MB.Block
   is
   begin
      return MB.Block'(Address            => B.Address,
                       Prev_Block_Address => B.Header.Prev_Block_Address,
                       Size               => B.Header.Size);
   end To_Model;

   --------------------------
   -- Set_Block_At_Address --
   --------------------------

   procedure Store_Block 
     (Ctx : TC.Context; B : Block)
     with SPARK_Mode => Off
   is
      use type SSE.Integer_Address;
      
      Hdr : BT.Block_Header with Address =>
        SSE.To_Address (SSE.To_Integer (Ctx.Memory.Base) + 
                            SSE.Integer_Address (B.Address)); 
   begin
      Hdr := B.Header;
   end Store_Block;
   
   
   -----------------
   -- Split_Block --
   -----------------
   
   procedure Split_Block (Ctx         : TC.Context;
                          B           : Block;
                          Left_Size,
                          Right_Size  : BT.Aligned_Size;
                          Left, Right : out Block)
   is
      
      use type MB.Block;
      use type MB.Formal_Model;
      
      New_Model       : MB.Formal_Model with Ghost;
      B_Left, B_Right : MB.Block := To_Model (Ctx, B) with Ghost;
   begin
      Left := Block'(Address => B.Address,
                     Header  => BT.Block_Header_Free'(Status             => BT.Free,
                                                      Prev_Block_Address => B.Header.Prev_Block_Address,
                                                      Size               => Left_Size, 
                                                      Free_List          => BT.Empty_Free_List));
      Right := Block'(Address => Next_Block_Address (Ctx, Left),
                      Header  => BT.Block_Header_Free'(Status             => BT.Free,
                                                       Prev_Block_Address => Left.Address,
                                                       Size               => Right_Size,
                                                       Free_List          => BT.Empty_Free_List));
      
      pragma Assert (Valid_Block (Ctx, Left));
      pragma Assert (Valid_Block (Ctx, Right));
      
      MB.Split_Block (M       => MC.Get_Block_Model (Ctx),
                      B       => To_Model (Ctx, B),
                      L_Size  => Left_Size,
                      R_Size  => Right_Size,
                      B_Left  => B_Left,
                      B_Right => B_Right,
                      New_M   => New_Model);
      
      MC.Set_Block_Model (Ctx, New_Model);
      
      -- proof that new blocks have their model counterparts
      pragma Assert (To_Model (Ctx, Left) = B_Left);
      pragma Assert (To_Model (Ctx, Right) = B_Right);
      
      pragma Assert (MB.Valid (New_Model));
      pragma Assert (MB.In_Model (New_Model, B_Left));
      pragma Assert (MB.In_Model (New_Model, B_Right));

      pragma Assert (MC.Get_Block_Model (Ctx) = New_Model);
      
      MB.Equality_Preserves_Validity (New_Model, MC.Get_Block_Model (Ctx));
      
      pragma Assert (MB.Valid (MC.Get_Block_Model (Ctx)));
      
      pragma Assert (MB.In_Model (MC.Get_Block_Model (Ctx),
                     To_Model (Ctx, Left)));

      pragma Assert (MB.In_Model (MC.Get_Block_Model (Ctx),
                     To_Model (Ctx, Right)));

      Store_Block (Ctx, Left);
      Store_Block (Ctx, Right);
      
   end Split_Block;
end TLSF.Block.Operations;
