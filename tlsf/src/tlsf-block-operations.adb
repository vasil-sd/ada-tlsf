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

   --------------------
   -- Get_Next_Block --
   --------------------
   
   procedure Get_Next_Block (Ctx  : TC.Context;
                             B    : Block;
                             Next : out Block)
   is
   begin
      Load_Block (Ctx, Next_Block_Address (Ctx, B), Next);
      -- proof of reflection of Next in model
      pragma Assert (To_Model (Ctx, Next).Address = Next.Address);
      pragma Assert (MB.In_Model (MC.Get_Block_Model (Ctx), To_Model (Ctx, Next)));
      pragma Assert (MB.In_Model (MC.Get_Block_Model (Ctx),
                     MB.Get_Next (MC.Get_Block_Model (Ctx),
                       To_Model (Ctx, B))));
      pragma Assert (To_Model (Ctx, Next).Address = MB.Get_Next (MC.Get_Block_Model (Ctx), To_Model (Ctx, B)).Address);
      -- use Lemma
      MB.Addresses_Equality_Implies_Blocks_Equality 
        (MC.Get_Block_Model (Ctx), 
         To_Model (Ctx, Next),
         MB.Get_Next (MC.Get_Block_Model (Ctx), To_Model (Ctx, B)));
      pragma Assert (To_Model (Ctx, Next) = MB.Get_Next (MC.Get_Block_Model (Ctx), To_Model (Ctx, B)));
   end Get_Next_Block;
   
   -----------------
   -- Store_Block --
   -----------------

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
   
   ----------------
   -- Load_Block --
   ----------------
   
   procedure Load_Block (Ctx  : TC.Context;
                         Addr : BT.Aligned_Address; 
                         B    : out Block)
     with SPARK_Mode => Off
   is
      use type SSE.Integer_Address;
      
      Hdr : BT.Block_Header with Address =>
        SSE.To_Address (SSE.To_Integer (Ctx.Memory.Base) + 
                            SSE.Integer_Address (Addr)); 
   begin
      B := Block'(Address => Addr,
                  Header  => Hdr);
   end Load_Block;
 
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
      
      Next : Block := B;
      
      B_Is_Last_Block : constant Boolean := Is_Last_Block(Ctx, B);
   begin
      
      if not B_Is_Last_Block then
         Get_Next_Block (Ctx, B, Next);
      end if;
      
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

      pragma Assert (Is_Last_Block(Ctx, Right) = B_Is_Last_Block);
      
      if not B_Is_Last_Block then
         Next.Header.Prev_Block_Address := Right.Address;
         pragma Assert (MC.Get_Block_Model (Ctx) = New_Model);
         pragma Assert (Next.Address = Next_Block_Address (Ctx, B));         
         MB.Equality_Preserves_Block_Relations (MC.Get_Block_Model (Ctx), New_Model, B_Right);
         pragma Assert (MB.Get_Next (New_Model, B_Right) = MB.Get_Next (MC.Get_Block_Model (Ctx), B_Right));
         pragma Assert (MB.Get_Next (New_Model, B_Right) = To_Model (Ctx, Next));
         pragma Assert (MB.Get_Next (MC.Get_Block_Model (Ctx), B_Right) = To_Model (Ctx, Next));
         pragma Assert (MB.In_Model (MC.Get_Block_Model (Ctx), To_Model(Ctx, Next)));
         pragma Assert (MB.Neighbor_Blocks (To_Model (Ctx, Right), To_Model (Ctx, Next)));
         Store_Block (Ctx, Next);
      end if;

   end Split_Block;
end TLSF.Block.Operations;
