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
          enum msg_req_rsp_type = {erply, espec, idle_r_r, nack, rdex, rdsh, srply, sspec, upack, upgrd, wack, wb, wbbak}
        Pre-state:
          net_req_rsp_kind = [[0, idle_r_r]]
        Action: p_req(p=0)
      Counterexample (TR):
        Theory:
          enum msg_req_rsp_type = {erply, espec, idle_r_r, nack, rdex, rdsh, srply, sspec, upack, upgrd, wack, wb, wbbak}
        Pre-state:
          net_req_rsp_kind = [[0, idle_r_r]]
        Action: p_req(p=0)
        Post-state:
          net_req_rsp_kind = [[0, rdsh]]
-/
#guard_msgs in
#check_invariants

end bar_mod
