
-- MSI protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  request_chanel: 0;                -- low priority
  response_chanel: 1;
  QMax: 2;
  NumVCs: 2;
  NetMax: 8;--ProcCount+1
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: request_chanel..NumVCs-1;
  Ack_Cnt: -ProcCount..ProcCount; -- IN P_IM_AD, when data do not arrive, but inv-ack arrive first
  MessageType: enum {  
                        GetS,
                        -- GetSAck,
                        GetM,
                        -- GetMAck,
                        Data,
                        E_Data,
                        FwdGetS,
            
                        FwdGetM,
                        -- FwdGetMAck,
                        FwdAck,

                        Inv,
                        InvAck,
                        PutS,
                        -- PutSAck,
                        PutM,
                        PutO,
                        PutE,
                        Ack_Count,
                        
                        NACK,
                        -- PutMAck,       
                        PutAck       
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      vc: VCType;
      val: Value;
      ack_cnt: Ack_Cnt;
      fwd: Node;
    End;

  HomeState:
    Record
      state: enum { H_I, H_S, H_E, H_M, H_O, 					--stable states
      				 H_SM_A, H_MM_A, H_EM_A, H_EO_A,H_OO_A, H_OM_oA_A, H_OM_A, H_OM_oA, H_MO_A}; --H_MS_A,  H_ES_A,								--transient states during recall
      owner: Node;	
      sharers: multiset [ProcCount] of Node;    --No need for sharers in this protocol, but this is a good way to represent them
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { P_I, P_IS_D, P_IM_A_D, P_IM_A,P_IM_D,
                    P_S, P_SM_A_D, P_SM_A, P_SM_D,
                    P_E,
                    P_O,
                    P_OM_AC,
                    P_OM_A,
                    P_OI_A,
                    P_M, P_MI_A,  P_EI_A, P_SI_A, P_II_A
                  };
      val: Value;
      ack_cnt: Ack_Cnt;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
    Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
    InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(
        mtype:MessageType;
	      dst:Node;
	      src:Node;
        vc:VCType;
        val:Value;
        ack_cnt:Ack_Cnt ;
        fwd: Node;

         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.ack_cnt :=ack_cnt;
  msg.fwd :=fwd;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
put "\n====================Error Msg====================\n";
  put "mtype: "; put msg.mtype;
  put "\n";
  put "src: "; put msg.src;
  put "\n";
  put "src_state: ";
  if IsMember(msg.src, Proc) then
    put Procs[msg.src].state;
  else
    put HomeNode.state;
  endif;
  put "dst_state: ";
  if IsMember(n, Proc) then
    put Procs[n].state;
  else
    put HomeNode.state;
  endif;
  put "\n";
  error " ahhUnhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

-- These aren't needed for Valid/Invalid protocol, but this is a good way of writing these functions
Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        Send(Inv, n, HomeType, request_chanel, UNDEFINED, UNDEFINED, rqst);
        -- Send invalidation message here 
      endif;
    endif;
  endfor;
End;



Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  cnt := MultiSetCount(i:HomeNode.sharers, true);


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case H_I:
    switch msg.mtype

    case GetS:
      HomeNode.state := H_E;
       HomeNode.owner := msg.src;
      Send(E_Data, msg.src, HomeType, response_chanel, HomeNode.val, cnt, UNDEFINED);
    case GetM:
      HomeNode.state := H_M;
      HomeNode.owner := msg.src;

      Send(Data, msg.src, HomeType, response_chanel, HomeNode.val, cnt, UNDEFINED);
    case PutS:
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    case PutM:
      Assert (HomeNode.owner != msg.src) "error: src is owner when HomeNode state is Invalid:PutM";
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED); 
    case PutO:
      Assert (HomeNode.owner != msg.src) "error: src is owner when HomeNode state is Invalid:PutO";
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED); 
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_S:
    -- Assert (IsUndefined(HomeNode.owner) = false) 
    --    "HomeNode has no owner, but line is Valid";
    switch msg.mtype

    case GetS:
      AddToSharersList(msg.src);   
      Send(Data, msg.src, HomeType, response_chanel, HomeNode.val, cnt, UNDEFINED);
      
    case GetM:
    	-- assert (msg.src = HomeNode.owner) "get from non-owner";
      
      if(IsSharer(msg.src))
      then
        if(cnt=1)
        then
        HomeNode.state := H_M;
        HomeNode.owner := msg.src;
        undefine HomeNode.sharers;
        Send(Data, msg.src, HomeType, response_chanel, HomeNode.val, 0, UNDEFINED);
        else
        HomeNode.state := H_SM_A;
        HomeNode.owner := msg.src;
        SendInvReqToSharers(msg.src);
        

        -- undefine HomeNode.sharers;
        Send(Data, msg.src, HomeType, response_chanel, HomeNode.val, cnt-1, UNDEFINED);
        RemoveFromSharersList(msg.src);
        endif;
      else
        HomeNode.state := H_SM_A;
        HomeNode.owner := msg.src;
        SendInvReqToSharers(msg.src);
        -- undefine HomeNode.sharers;
        Send(Data, msg.src, HomeType, response_chanel, HomeNode.val, cnt, UNDEFINED);
        -- endif;
      endif;
      

    case PutS:
    
    if(IsSharer(msg.src))
      then
      if(cnt=1)
      then
      HomeNode.state := H_I;
      undefine HomeNode.sharers;
      undefine HomeNode.owner;
      endif;
    endif;
    Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    RemoveFromSharersList(msg.src);

    case PutM:
      assert (msg.src != HomeNode.owner) "Writeback from owner rather than nonOwner:PUTM";
      if(IsSharer(msg.src)) -- because  P_state can be changed from P_MI_A to P_SI_A(fwdgetS)
        then
        if(cnt=1)
        then
        HomeNode.state := H_I;
        undefine HomeNode.sharers;
        endif;
      endif;
      RemoveFromSharersList(msg.src);
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    
    case PutO:
      assert (msg.src != HomeNode.owner) "Writeback from owner rather than nonOwner:PutO";
      if(IsSharer(msg.src)) -- because  P_state can be changed from P_MI_A to P_SI_A(fwdgetS)
        then
        if(cnt=1)
        then
        HomeNode.state := H_I;
        undefine HomeNode.sharers;
        endif;
      endif;
      RemoveFromSharersList(msg.src);
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case H_O:
    switch msg.mtype
    case GetS:
      if(msg.src !=HomeNode.owner)
      then
        Send(FwdGetS, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
        AddToSharersList(msg.src);
        -- AddToSharersList(HomeNode.owner);
        HomeNode.state := H_OO_A;
      else
        ErrorUnhandledMsg(msg, HomeType);
      endif;

    case GetM:
      if(msg.src=HomeNode.owner)
      then
        if(cnt=0)
        then
          HomeNode.state := H_OM_oA;
          -- Send(Data, msg.src, HomeType, response_chanel, UNDEFINED, 0,UNDEFINED);
          Send(Ack_Count, msg.src, HomeType, response_chanel, UNDEFINED, 0,UNDEFINED);
        else  
          HomeNode.state := H_OM_oA_A;
          -- Send(Data, msg.src, HomeType, response_chanel, UNDEFINED, cnt,UNDEFINED);
          Send(Ack_Count, msg.src, HomeType, response_chanel, UNDEFINED, cnt,UNDEFINED);
          SendInvReqToSharers(msg.src)
        endif;
      else
        if(IsSharer(msg.src))
        then
          if(cnt=1)
          then
            Send(FwdGetM, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
            Send(Ack_Count, msg.src, HomeType, response_chanel, UNDEFINED, 0,UNDEFINED);
            HomeNode.state := H_OM_oA;
            HomeNode.owner := msg.src;
            undefine HomeNode.sharers;
          else
            HomeNode.state := H_OM_oA_A;
            Send(Ack_Count, msg.src, HomeType, response_chanel, UNDEFINED, cnt-1,UNDEFINED);
            SendInvReqToSharers(msg.src);
            Send(FwdGetM, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
            RemoveFromSharersList(msg.src);
            HomeNode.owner := msg.src;
          endif;
        else
          if(cnt=0)
          then
            Send(Ack_Count, msg.src, HomeType, response_chanel, UNDEFINED, cnt,UNDEFINED);
            Send(FwdGetM, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
            HomeNode.state := H_OM_oA;
            HomeNode.owner := msg.src;
            
          else
            Send(Ack_Count, msg.src, HomeType, response_chanel, UNDEFINED, cnt,UNDEFINED);
            Send(FwdGetM, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
            HomeNode.state := H_OM_oA_A;
            HomeNode.owner := msg.src;
            SendInvReqToSharers(msg.src);
          endif;
          
          
          -- endif;
        endif;
      endif;

    case PutS:--H_O allow only one owner and no sharer,also in H_O rather than H_I
      
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      RemoveFromSharersList(msg.src);

    case PutM:
      if(msg.src=HomeNode.owner)
      then
        if(cnt=0)
        then
          RemoveFromSharersList(msg.src);
          HomeNode.val := msg.val;
          Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
          undefine HomeNode.owner;
          HomeNode.state := H_I;
        else
          RemoveFromSharersList(msg.src);
          HomeNode.val := msg.val;
          Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
          undefine HomeNode.owner;
          HomeNode.state := H_S;
        endif;
        
      else
        RemoveFromSharersList(msg.src);
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      endif;
    case PutO:
      if(msg.src=HomeNode.owner)
      then
        HomeNode.val := msg.val;
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
        undefine HomeNode.owner;
        if(cnt=0)
        then
          HomeNode.state := H_I;
        else
          HomeNode.state := H_S;
        endif
      else
        -- RemoveFromSharersList(msg.src);
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      endif;
    else

      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    endswitch


  case H_M:
    switch msg.mtype
   
    case GetS:
      Send(FwdGetS, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
      AddToSharersList(msg.src);
     -- AddToSharersList(HomeNode.owner);
      HomeNode.state := H_MO_A;

    case GetM:
      HomeNode.state := H_MM_A;
      Send(FwdGetM, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
      HomeNode.owner :=msg.src;

    case PutS:
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);

    case PutM:
      if(HomeNode.owner=msg.src)
      then
        HomeNode.val := msg.val;
        undefine HomeNode.owner;
        undefine HomeNode.sharers;
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
        HomeNode.state := H_I;
      else
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      endif;
    case PutO:
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);

    else
    

       ErrorUnhandledMsg(msg, HomeType);
    endswitch

case H_E:
    switch msg.mtype
   
    case GetS:
      Send(FwdGetS, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
      AddToSharersList(msg.src);
      -- AddToSharersList(HomeNode.owner);
      HomeNode.state := H_EO_A;

    case GetM:

      HomeNode.state := H_EM_A;
      Send(FwdGetM, HomeNode.owner, HomeType, request_chanel, UNDEFINED, UNDEFINED, msg.src);
      HomeNode.owner :=msg.src;

    case PutS:
      Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);

    case PutM:
      if(HomeNode.owner=msg.src)
      then
        HomeNode.val := msg.val;
        undefine HomeNode.owner;
        undefine HomeNode.sharers;
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
        HomeNode.state := H_I;
      else
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      endif;

    case PutE:
      if(HomeNode.owner=msg.src)
      then
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
        undefine HomeNode.owner;
        undefine HomeNode.sharers;
        HomeNode.state := H_I;
      else
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      endif

    case PutO:
      if(HomeNode.owner=msg.src)
      then
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
        undefine HomeNode.owner;
        undefine HomeNode.sharers;
        HomeNode.state := H_I;
      else
        Send(PutAck, msg.src, HomeType, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      endif
    
    else
       ErrorUnhandledMsg(msg, HomeType);
    endswitch

  case H_SM_A:
    switch msg.mtype
      case GetS:
        msg_processed := false; -- stall message in InBox
      case GetM:
        msg_processed := false; -- stall message in InBox
      case PutS:
        msg_processed := false; -- stall message in InBox
      case PutM:
        msg_processed := false; -- stall message in InBox
      case PutO:
        msg_processed := false; -- stall message in InBox
      case InvAck:
        if(IsSharer(msg.src))
        then
        if(cnt=1)
        then
        HomeNode.state := H_M;
        undefine HomeNode.sharers;
        endif;
         endif;
         RemoveFromSharersList(msg.src);
      else
        ErrorUnhandledMsg(msg, HomeType);
    endswitch
      

  case H_MO_A:
      switch msg.mtype
        

        case FwdAck:
        HomeNode.state := H_O;
        HomeNode.val := msg.val;
          -- if(HomeNode.owner=msg.src)
          -- then
          --     HomeNode.state := H_S;
          -- endif;
        case GetS:
          msg_processed := false; -- stall message in InBox
        case GetM:
          msg_processed := false; -- stall message in InBox
        case PutS:
          msg_processed := false; -- stall message in InBox
        case PutM:
          msg_processed := false; -- stall message in InBox
        case PutO:
          msg_processed := false; -- stall message in InBox
        else
        ErrorUnhandledMsg(msg, HomeType);
      endswitch

  case H_MM_A:
      switch msg.mtype
        case FwdAck:
        HomeNode.state := H_M;

        case GetS:
          msg_processed := false; -- stall message in InBox
        case GetM:
          msg_processed := false; -- stall message in InBox

        case PutS:
          msg_processed := false; -- stall message in InBox
        case PutM:
          msg_processed := false; -- stall message in InBox
        case PutO:
          msg_processed := false; -- stall message in InBox
        else
        ErrorUnhandledMsg(msg, HomeType);
      endswitch      
  
    case H_EO_A:
      switch msg.mtype
        case FwdAck:
        HomeNode.state := H_O;
        HomeNode.val := msg.val;
        case GetS:
          msg_processed := false; -- stall message in InBox
        case GetM:
          msg_processed := false; -- stall message in InBox
        case PutS:
          msg_processed := false; -- stall message in InBox
        case PutM:
          msg_processed := false; -- stall message in InBox
        case PutO:
          msg_processed := false; -- stall message in InBox
        else
        ErrorUnhandledMsg(msg, HomeType);
      endswitch

    case H_EM_A:
      switch msg.mtype
        case FwdAck:
        HomeNode.state := H_M;
        case GetS:
          msg_processed := false; -- stall message in InBox
        case GetM:
          msg_processed := false; -- stall message in InBox
        case PutS:
          msg_processed := false; -- stall message in InBox
        case PutM:
          msg_processed := false; -- stall message in InBox
        case PutO:
          msg_processed := false; -- stall message in InBox
        else
        ErrorUnhandledMsg(msg, HomeType);
      endswitch

    case H_OO_A:
     switch msg.mtype
    

        case FwdAck:
          HomeNode.state := H_O;
          HomeNode.val  :=msg.val;
          

        case GetS:
          msg_processed := false; -- stall message in InBox
        case GetM:
          msg_processed := false;
        case PutS:
          msg_processed := false; -- stall message in InBox
        case PutM:
          msg_processed := false; -- stall message in InBox
        case PutO:
          msg_processed := false; -- stall message in InBox
        else
        ErrorUnhandledMsg(msg, HomeType);
      endswitch
    
    case H_OM_A:
      switch msg.mtype
      case GetS:
        msg_processed := false; -- stall message in InBox
      case GetM:
        msg_processed := false; -- stall message in InBox
      case PutS:
        msg_processed := false; -- stall message in InBox
      case PutM:
        msg_processed := false; -- stall message in InBox
      case PutO:
        msg_processed := false; -- stall message in InBox
      case InvAck:
        if(IsSharer(msg.src))
        then
          if(cnt=1)
          then
          HomeNode.state := H_M;
          undefine HomeNode.sharers;
          endif;
        endif;
         RemoveFromSharersList(msg.src);
      else
        ErrorUnhandledMsg(msg, HomeType);
      endswitch

    case H_OM_oA:
      switch msg.mtype
        case GetS:
          msg_processed := false; -- stall message in InBox
        case GetM:
          msg_processed := false; -- stall message in InBox
        case PutS:
          msg_processed := false; -- stall message in InBox
        case PutM:
          msg_processed := false; -- stall message in InBox
        case PutO:
          msg_processed := false; -- stall message in InBox
        case FwdAck:
          HomeNode.state := H_M;
          HomeNode.val := msg.val;
        else
          ErrorUnhandledMsg(msg, HomeType);
      endswitch

    case H_OM_oA_A:
      switch msg.mtype
      case GetS:
        msg_processed := false; -- stall message in InBox
      case GetM:
        msg_processed := false; -- stall message in InBox
      case PutS:
        msg_processed := false; -- stall message in InBox
      case PutM:
        msg_processed := false; -- stall message in InBox
      case PutO:
        msg_processed := false; -- stall message in InBox
      case FwdAck:
        HomeNode.state := H_OM_A;
        HomeNode.val := msg.val;
      case InvAck:
        if(IsSharer(msg.src))
        then
          if(cnt=1)
          then
          HomeNode.state := H_OM_oA;
          undefine HomeNode.sharers;
          endif;
        endif;
         RemoveFromSharersList(msg.src);
      else
        ErrorUnhandledMsg(msg, HomeType);
    endswitch
      



  endswitch;
  
End;


Procedure ProcReceive(msg:Message; p:Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do
  alias pack_count:Procs[p].ack_cnt do 

  switch ps
  case P_I:
  switch msg.mtype
    case Data:

    else
    ErrorUnhandledMsg(msg, p);
  endswitch;

  case P_IS_D:
    switch msg.mtype
    --   case NACK:
    --       Send(GetS, HomeType, p, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      case Data:
        pv := msg.val;
        ps := P_S;
      case E_Data:
        pv := msg.val;
        ps := P_E;
      case Inv:
        msg_processed := false; -- stall message in InBox
      case FwdGetS:
        msg_processed := false;
      case FwdGetM:
        msg_processed := false;
      else
        ErrorUnhandledMsg(msg, p);
    endswitch;

  case P_IM_A_D:
     switch msg.mtype
    --  case NACK:
    --       Send(GetM, HomeType, p, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      case Ack_Count:
        pack_count :=pack_count+msg.ack_cnt;
        if(pack_count=0)
        then
          ps:=P_IM_D;
        
        endif;
      case Data:
        pv := msg.val;
      if(msg.src=HomeType)
      then
        if(msg.ack_cnt=0)
        then
            ps := P_M;
        else
          pack_count :=pack_count+msg.ack_cnt;
          if(pack_count=0)
            then
              ps := P_M;
          else
              ps := P_IM_A;
            endif;
        endif;
      else
        if(!IsUndefined(msg.ack_cnt) & msg.ack_cnt=0)
        then
          ps := P_M;
        else
          -- if()
          -- then
          ps := P_IM_A;
          -- endif;
        endif;
        
      endif;
      case FwdGetS:
        msg_processed := false; -- stall message in InBox
      case FwdGetM:
        msg_processed := false; -- stall message in InBox
      case InvAck:
        pack_count :=pack_count-1;
        if(pack_count=0)
        then
          ps:=P_IM_D;
        endif;
      else
        ErrorUnhandledMsg(msg, p);
    endswitch;


  case P_IM_A:    

    switch msg.mtype
    case FwdGetS:
        msg_processed := false; -- stall message in InBox
    case FwdGetM:
        msg_processed := false; -- stall message in InBox
    case InvAck:
        pack_count :=pack_count-1;
        if(pack_count=0)
        then
          ps :=P_M;
        endif;
    case Ack_Count:
      
      pack_count :=pack_count+msg.ack_cnt;
      if(pack_count=0)
      then
        ps :=P_M;
      endif;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  case P_S:
    switch msg.mtype
    case Inv:
      Send(InvAck, msg.fwd, p, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      Send(InvAck, HomeType, p, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := P_I;
      undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;
  
  case P_SM_A_D:
    switch msg.mtype
    -- case NACK:
    --       Send(GetS, HomeType, p, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    case FwdGetS:
        msg_processed := false; -- stall message in InBox
    case FwdGetM:
        msg_processed := false; -- stall message in InBox
    case Inv:
      Send(InvAck, msg.fwd, p, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      Send(InvAck, HomeType, p, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      ps:=P_IM_A_D;

    case Ack_Count:
      pack_count :=pack_count+msg.ack_cnt;
      if(pack_count=0)
      then
        -- pack_count :=pack_count+msg.ack_cnt;
        ps:=P_SM_D
      -- else
      --   pack_count :=pack_count+msg.ack_cnt;
      endif;
      
    case Data:
        pv :=msg.val;
     if(msg.src=HomeType)
      then
        if(msg.ack_cnt=0)
        then
          ps := P_M;
        else
          pack_count :=pack_count+msg.ack_cnt;
            if(pack_count=0)
            then
              ps := P_M;
            else
              ps := P_SM_A;
            endif;
        endif;
      else
          ps := P_SM_A;
      endif;

    case InvAck:
        pack_count :=pack_count-1;
        if(pack_count=0)
        then
            ps := P_SM_D;
        endif;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  case P_SM_A:
    switch msg.mtype
    case FwdGetS:
        msg_processed := false; -- stall message in InBox
    case FwdGetM:
        msg_processed := false; -- stall message in InBox
    case Ack_Count:
      pack_count :=pack_count+msg.ack_cnt;
      if(pack_count=0)
      then
        ps := P_M;
      endif;
    case InvAck:
        pack_count :=pack_count-1;
        if(pack_count=0)
        then
              ps := P_M;
        endif;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;
  case P_IM_D:
    switch msg.mtype
    -- case NACK:
    --       Send(GetS, HomeType, p, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    case FwdGetS:
        msg_processed := false; -- stall message in InBox
    case FwdGetM:
        msg_processed := false; -- stall message in InBox
    case Data:
        pv :=msg.val;
     if(msg.src != HomeType)
      then
         ps := P_M;
      endif;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  case P_SM_D:
    switch msg.mtype
    case Ack_Count:
    
    case InvAck:

    case Inv:
        msg_processed := false; -- stall message in InBox
    -- case NACK:
    --       Send(GetM, HomeType, p, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    case FwdGetS:
        msg_processed := false; -- stall message in InBox
    case FwdGetM:
        msg_processed := false; -- stall message in InBox
    case Data:
        pv :=msg.val;
     if(msg.src != HomeType)
      then
         ps := P_M;
      endif;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  case P_M:
    switch msg.mtype
    case FwdGetS:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        ps := P_O;
    case FwdGetM:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED); 
        Send(Data, msg.fwd, p, response_chanel, pv, 0, UNDEFINED); 
        ps := P_I;
        undefine pv;
    case Ack_Count:

    
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;
  case P_E:
    switch msg.mtype
    case FwdGetS:
      Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
      Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
      ps := P_O;
    
    case FwdGetM:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED); 
        Send(Data, msg.fwd, p, response_chanel, pv, 0, UNDEFINED); 
        ps := P_I;
        undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

  case P_MI_A:
    switch msg.mtype
    case FwdGetS:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        ps := P_OI_A;
    case FwdGetM:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED); 
        -- Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED); 
        Send(Data, msg.fwd, p, response_chanel, pv, 0, UNDEFINED);
        ps := P_II_A;
        undefine pv;
    case PutAck:
        ps := P_I;
        undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  case P_O:
    switch msg.mtype
    case FwdGetS:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
    case FwdGetM:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED); 
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        ps := P_I;
        undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

    case P_OM_AC:
    switch msg.mtype
    -- case Data:
    case FwdGetS:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
     
        -- Send(GetM, HomeType, p, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        -- ps := P_SM_A_D;
        --  msg_processed := false; -- stall message in InBox
    case FwdGetM:
        
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        ps := P_IM_A_D;
        undefine pv;
        --  msg_processed := false; -- stall message in InBox
    case Ack_Count:
      if(msg.ack_cnt=0)
      then
        ps := P_M;
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
      else
        
        pack_count :=pack_count+msg.ack_cnt;
        if(pack_count=0)
        then
          ps := P_M;
          Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        else
          ps := P_OM_A;
        endif;
        
      endif;
      
    case InvAck:
        pack_count :=pack_count-1;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

    case P_OM_A:
    switch msg.mtype
    case FwdGetS:
        -- Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        -- Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        msg_processed := false; -- stall message in InBox
    case FwdGetM:
        msg_processed := false; -- stall message in InBox
    case InvAck:
        pack_count :=pack_count-1;
        if(pack_count=0)
        then
              ps := P_M;
              Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        endif;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

    case P_OI_A:
    switch msg.mtype
    case FwdGetS:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
    case FwdGetM:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED); 
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED); --
        ps := P_II_A;
        undefine pv;
    case PutAck:
        ps := P_I;
        undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;


  case P_EI_A:
    switch msg.mtype
    case FwdGetS:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED);
        ps := P_OI_A;
    case FwdGetM:
        Send(FwdAck, HomeType, p, response_chanel, pv, UNDEFINED, UNDEFINED); 
        -- Send(Data, msg.fwd, p, response_chanel, pv, UNDEFINED, UNDEFINED); 
        Send(Data, msg.fwd, p, response_chanel, pv, 0, UNDEFINED);
        ps := P_II_A;
        undefine pv;
    case PutAck:
        ps := P_I;
        undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  case P_SI_A:
    switch msg.mtype
    case Inv:
      Send(InvAck, msg.fwd, p, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      Send(InvAck, HomeType, p, response_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
      undefine pv;
      ps := P_II_A;
    case PutAck:
        ps := P_I;
        undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;

  case P_II_A:
    switch msg.mtype
    case PutAck:
        ps := P_I;
        undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
	endswitch;
  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
  
  endalias;
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

ruleset n:Proc Do
  alias p:Procs[n] Do

	ruleset v:Value Do
  	rule "store from M to M "
   	 (p.state = P_M)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
  	endrule;
	endruleset;

  rule "read from I to S or E"
    (p.state = P_I) 
  ==>
    Send(GetS, HomeType, n, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    p.state := P_IS_D;
  endrule;

  rule "store from I to M"
    (p.state = P_I) 
  ==>
    Send(GetM, HomeType, n, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    p.state := P_IM_A_D;

  endrule;
  rule "store from E to M"
    (p.state = P_E) 
  ==>
    -- Send(GetM, HomeType, n, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    p.state := P_M;

  endrule;

  rule "store from S to M"
    (p.state = P_S) 
  ==>
    Send(GetM, HomeType, n, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    p.state := P_SM_A_D;

  endrule;

  rule "store from O to M"
    (p.state = P_O) 
  ==>
    Send(GetM, HomeType, n, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED);
    p.state := P_OM_AC;

  endrule;

  rule "writeback from M to I"
    (p.state = P_M)
  ==>
    Send(PutM, HomeType, n, request_chanel, p.val, UNDEFINED, UNDEFINED); 
    p.state := P_MI_A;
    -- undefine p.val;
  endrule;

  rule "writeback from O to I"
    (p.state = P_O)
  ==>
    Send(PutO, HomeType, n, request_chanel, p.val, UNDEFINED, UNDEFINED); 
    p.state := P_OI_A;
    -- undefine p.val;
  endrule;

   rule "writeback from E to I"
    (p.state = P_E)
  ==>
    Send(PutM, HomeType, n, request_chanel, p.val, UNDEFINED, UNDEFINED); 
    p.state := P_EI_A;
    -- undefine p.val;
  endrule;

  rule "writeback from S to I"
    (p.state = P_S)
  ==>
    Send(PutS, HomeType, n, request_chanel, UNDEFINED, UNDEFINED, UNDEFINED); 
    p.state := P_SI_A;
    undefine p.val;
  endrule;

  endalias;
endruleset;

-- Message delivery rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do

		-- Pick a random message in the network and delivier it
    rule "receive-net"
			(isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
	    endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
	  		box[msg.vc] := msg;
			endif;
	  
		  MultiSetRemove(midx, chan);
	  
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

	-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
	ruleset vc:VCType do
    rule "receive-blocked-vc"
			(! isundefined(InBox[n][vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(InBox[n][vc]);
      else
        ProcReceive(InBox[n][vc], n);
			endif;

			if msg_processed
			then
				-- Message has been handled, forget it
	  		undefine InBox[n][vc];
			endif;
	  
    endrule;
  endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

	For v:Value do
  -- home node initialization
  HomeNode.state := H_I;
  undefine HomeNode.owner;
  undefine HomeNode.sharers;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := P_I;
    Procs[i].ack_cnt :=0;
    undefine Procs[i].val;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "HomeNode.state is in I or S implies empty owner"
  (HomeNode.state = H_I | HomeNode.state = H_S)
    ->
      IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid"
     HomeNode.state = H_I
    ->
			HomeNode.val = LastWrite;

invariant "P.state is in S or M or E match last write"
  Forall n : Proc Do	
     (Procs[n].state = P_S | Procs[n].state = P_M |Procs[n].state = P_E) --  
    ->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
            -- put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
            -- put " at home -- "; put HomeNode.state;
	end;
	
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = P_I
    ->
			IsUndefined(Procs[n].val)
	end;
	

-- Here are some invariants that are helpful for validating shared state.

-- invariant "modified or E implies empty sharers list"
--   HomeNode.state = H_M |  HomeNode.state = H_E
--     ->
--       MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Homenode.state is in I or M or E implies empty sharer list"
  (HomeNode.state = H_I | HomeNode.state = H_M |  HomeNode.state = H_E)
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do	
     (HomeNode.state = H_S | HomeNode.state = H_I ) --|  HomeNode.state = H_I | HomeNode.state = H_E
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state or E match memory"
  Forall n : Proc Do	
     HomeNode.state = H_S & Procs[n].state = P_S | HomeNode.state = H_E & Procs[n].state = P_E
    ->
			HomeNode.val = Procs[n].val
	end;

