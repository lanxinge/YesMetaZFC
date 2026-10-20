import YesMetaZFC.SetTheory.LargeCardinal.TypeGameTrace

/-! # 实数前缀与同一原历史逐点对应

只保留前缀中实际出现的事件；事件公式限制在反射层内，因而可沿偶数
嵌入搬运。两份前缀在共同历史中的一致性由时钟和历史函数的单值性给出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_play_body0_m : Formula 1 4 := .forallE (.forallE
  (.imp (rd_entry0_m (.bound 1) .newest (.bound 5))
    (tg_event_m (.bound 2) (.bound 1) (.bound 3) (.bound 4) .newest)))

theorem tg_play_body0_closed_l : tg_play_body0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_play_body0_m, Definitional.Formula.FreeClosed]

def tg_play0_m : Formula 1 5 := .conj (.mem (.bound 4) (.bound 0))
  (lr_rel_m tg_play_body0_m (.bound 0) (fun i => .bound i.succ))
theorem tg_play0_closed_l : tg_play0_m.FreeClosed :=
  ⟨⟨rfl, rfl⟩, lr_rel_closed_l _ tg_play_body0_closed_l _ _ rfl (fun _ => rfl)⟩
theorem tg_play0_delta_l : tg_play0_m.IsDelta0 := .conj (.mem ..) (lr_rel_delta_l ..)

def Tg_play_d (C c b h s : M.Domain) : Prop :=
  Formula.satisfies (⟨fun i => [C,c,b,h,s].get i, fun _ => C⟩ : Env M 5) tg_play0_m
def tg_play_m {d} (C c b h s : Term d) : Formula 1 d := tg_play0_m.bind (fun i => [C,c,b,h,s].get i)
@[simp] theorem tg_play_closed_l {d} (C c b h s : Term d)
    (hC : C.freeSupport = []) (hc : c.freeSupport = []) (hb : b.freeSupport = [])
    (hh : h.freeSupport = []) (hs : s.freeSupport = []) : (tg_play_m C c b h s).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _
    (Fin.cases hC (Fin.cases hc (Fin.cases hb (Fin.cases hh (Fin.cases hs (fun i => Fin.elim0 i)))))) _).mpr tg_play0_closed_l

theorem tg_play_sat_l {d} (ρ : Env M d) (C c b h s : Term d) : Formula.satisfies ρ (tg_play_m C c b h s) ↔
    Tg_play_d (C.eval ρ) (c.eval ρ) (b.eval ρ) (h.eval ρ) (s.eval ρ) := by
  rw [tg_play_m, Formula.satisfies_bind]
  apply Formula.closed_env_l _ tg_play0_closed_l
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) i

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

omit hZF in
theorem tg_play_read_l (hE : Extensional M) {C : M.Domain} (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (c b h s : (rt_model_l C nc).Domain) :
    Tg_play_d C c.val b.val h.val s.val ↔ ∀ i x, Rd_entry_d i x s → Tg_event_d J c i b h x := by
  let ρ : Env (rt_model_l C nc) 4 := ⟨fun i => [c,b,h,s].get i, fun _ => c⟩
  let η : Env M 5 := ⟨fun i => [C,c.val,b.val,h.val,s.val].get i, fun _ => C⟩
  have rel := sc_relative_sat_l ct nc tg_play_body0_m tg_play_body0_closed_l ρ η
    (.bound 0) (fun i => .bound i.succ) rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  change (M.mem s.val C ∧ Formula.satisfies η (lr_rel_m tg_play_body0_m (.bound 0) (fun i => .bound i.succ))) ↔ _
  rw [and_iff_right s.property, rel]
  simp only [tg_play_body0_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l (rt_model_ext_l hE ct nc), tg_event_sat_l J (rt_model_ext_l hE ct nc)]
  rfl

theorem Tg_play_d.mono_l {C s : M.Domain} (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (c b h h' : (rt_model_l C nc).Domain)
    (play : Tg_play_d C c.val b.val h.val s) (sub : M.MemberSubset h.val h'.val) : Tg_play_d C c.val b.val h'.val s := by
  have hs : M.mem s C := ((Formula.satisfies_conj_iff ..).mp play).1
  exact (tg_play_read_l hZF.1 ct nc J c b h' ⟨s,hs⟩).mpr fun i x hi =>
    ((tg_play_read_l hZF.1 ct nc J c b h ⟨s,hs⟩).mp play i x hi).mono_l J (fun p hp => sub p.val hp)

theorem Tg_play_d.map_l {ω X R d Y S e j C C' c c' b b' h h' s s' : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I d X R) (my : Smem_d I e Y S) (map : Smap_d I ω d e X Y j)
    (iC : Rd_entry_d C C' j) (ic : Rd_entry_d c c' j) (ib : Rd_entry_d b b' j)
    (ih : Rd_entry_d h h' j) (is : Rd_entry_d s s' j) (play : Tg_play_d C c b h s) : Tg_play_d C' c' b' h' s' :=
  (smap_delta_l I hZF hw xt yt mx my map tg_play0_m tg_play0_closed_l tg_play0_delta_l
    (⟨fun i => [C,c,b,h,s].get i, fun _ => C⟩ : Env M 5)
    (⟨fun i => [C',c',b',h',s'].get i, fun _ => C'⟩ : Env M 5)
    (Fin.cases iC (Fin.cases ic (Fin.cases ib (Fin.cases ih (Fin.cases is (fun i => Fin.elim0 i))))))).mp play

theorem Tg_play_d.entry_eq_l {C s t i x y : M.Domain} (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (ρ : Env (rt_model_l C nc) 46)
    (valid : Formula.satisfies ρ tg_issued0_m)
    (left : Tg_play_d C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val s)
    (right : Tg_play_d C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val t)
    (hi : Rd_entry_d i x s) (hy : Rd_entry_d i y t) : x = y := by
  have hs : M.mem s C := ((Formula.satisfies_conj_iff ..).mp left).1
  have ht : M.mem t C := ((Formula.satisfies_conj_iff ..).mp right).1
  have state := (tg_issued_sat_l J (rt_model_ext_l hZF.1 ct nc) ρ).mp valid
  have ix := rd_entry_transitive_l ct hs hi
  have iy := rd_entry_transitive_l ct ht hy
  have ex := (tg_play_read_l hZF.1 ct nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) ⟨s,hs⟩).mp left
    ⟨i,ix.1⟩ ⟨x,ix.2⟩ ((rt_entry_l ct nc hZF.1 _ _ _).mpr hi)
  have ey := (tg_play_read_l hZF.1 ct nc J (ρ.bound 4) (ρ.bound 3) (ρ.bound 20) ⟨t,ht⟩).mp right
    ⟨i,ix.1⟩ ⟨y,iy.2⟩ ((rt_entry_l ct nc hZF.1 _ _ _).mpr hy)
  exact congrArg Subtype.val (tg_control_event_unique_l J (rt_model_ext_l hZF.1 ct nc) _ state.control state.history ex ey)

theorem Tg_play_d.subset_l {C s t n m : M.Domain} (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (ρ : Env (rt_model_l C nc) 46)
    (valid : Formula.satisfies ρ tg_issued0_m)
    (left : Tg_play_d C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val s)
    (right : Tg_play_d C (ρ.bound 4).val (ρ.bound 3).val (ρ.bound 20).val t)
    (gs : Tg_graph_d I n s) (gt : Tg_graph_d I m t) (nm : M.MemberSubset n m) : M.MemberSubset s t := by
  intro p hp
  obtain ⟨i,x,pair⟩ := gs.1.1 p hp
  have hi : Rd_entry_d i x s := ⟨p,pair,hp⟩
  obtain ⟨y,hy⟩ := (gt.2 i).mp (nm i ((gs.2 i).mpr ⟨x,hi⟩))
  have eq := left.entry_eq_l hZF ct nc J ρ valid right hi hy
  obtain ⟨q,qp,hq⟩ := hy
  exact kpair_unique_l M hZF.1 qp (eq ▸ pair) ▸ hq

end YesMetaZFC.SetTheory.LargeCardinal
