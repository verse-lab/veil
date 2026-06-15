import Veil

veil module bar_mod

type proc
enum msg_req_rsp_type = {idle_r_r,erply,espec,nack,rdsh,rdex,srply,sspec,upack,upgrd,wack,wb,wbbak}

function net_req_rsp_kind : proc → msg_req_rsp_type

after_init {
net_req_rsp_kind P := idle_r_r
}

action p_req (p:proc) {
net_req_rsp_kind p := rdsh
}

invariant (net_req_rsp_kind P)=idle_r_r

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  p_req
    doesNotThrow ... ✅
    inv_0 ... ❌
      Counterexample (WP):
        Theory:
          msg_req_rsp_type_Enum.erply = bar_mod.msg_req_rsp_type_IndT.erply
          msg_req_rsp_type_Enum.espec = bar_mod.msg_req_rsp_type_IndT.espec
          msg_req_rsp_type_Enum.idle_r_r = bar_mod.msg_req_rsp_type_IndT.idle_r_r
          msg_req_rsp_type_Enum.nack = bar_mod.msg_req_rsp_type_IndT.nack
          msg_req_rsp_type_Enum.rdex = bar_mod.msg_req_rsp_type_IndT.rdex
          msg_req_rsp_type_Enum.rdsh = bar_mod.msg_req_rsp_type_IndT.rdsh
          msg_req_rsp_type_Enum.srply = bar_mod.msg_req_rsp_type_IndT.srply
          msg_req_rsp_type_Enum.sspec = bar_mod.msg_req_rsp_type_IndT.sspec
          msg_req_rsp_type_Enum.upack = bar_mod.msg_req_rsp_type_IndT.upack
          msg_req_rsp_type_Enum.upgrd = bar_mod.msg_req_rsp_type_IndT.upgrd
          msg_req_rsp_type_Enum.wack = bar_mod.msg_req_rsp_type_IndT.wack
          msg_req_rsp_type_Enum.wb = bar_mod.msg_req_rsp_type_IndT.wb
          msg_req_rsp_type_Enum.wbbak = bar_mod.msg_req_rsp_type_IndT.wbbak
        Pre-state:
          net_req_rsp_kind = [[0, bar_mod.msg_req_rsp_type_IndT.idle_r_r]]
        Action: p_req(p=0)
      Counterexample (TR):
        Theory:
          msg_req_rsp_type_Enum.erply = bar_mod.msg_req_rsp_type_IndT.erply
          msg_req_rsp_type_Enum.espec = bar_mod.msg_req_rsp_type_IndT.espec
          msg_req_rsp_type_Enum.idle_r_r = bar_mod.msg_req_rsp_type_IndT.idle_r_r
          msg_req_rsp_type_Enum.nack = bar_mod.msg_req_rsp_type_IndT.nack
          msg_req_rsp_type_Enum.rdex = bar_mod.msg_req_rsp_type_IndT.rdex
          msg_req_rsp_type_Enum.rdsh = bar_mod.msg_req_rsp_type_IndT.rdsh
          msg_req_rsp_type_Enum.srply = bar_mod.msg_req_rsp_type_IndT.srply
          msg_req_rsp_type_Enum.sspec = bar_mod.msg_req_rsp_type_IndT.sspec
          msg_req_rsp_type_Enum.upack = bar_mod.msg_req_rsp_type_IndT.upack
          msg_req_rsp_type_Enum.upgrd = bar_mod.msg_req_rsp_type_IndT.upgrd
          msg_req_rsp_type_Enum.wack = bar_mod.msg_req_rsp_type_IndT.wack
          msg_req_rsp_type_Enum.wb = bar_mod.msg_req_rsp_type_IndT.wb
          msg_req_rsp_type_Enum.wbbak = bar_mod.msg_req_rsp_type_IndT.wbbak
        Pre-state:
          net_req_rsp_kind = [[0, bar_mod.msg_req_rsp_type_IndT.idle_r_r]]
        Action: p_req(p=0)
        Post-state:
          net_req_rsp_kind = [[0, bar_mod.msg_req_rsp_type_IndT.rdsh]]
-/
#guard_msgs in
#check_invariants

end bar_mod
