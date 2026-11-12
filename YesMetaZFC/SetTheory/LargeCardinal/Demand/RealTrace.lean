import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.SetTheory.KP.Natural

/-! # 原关系中的实数短图与完整历史

第一辅助时刻为一，实数时刻为它的后继。短图的每个函数值都对应
同一历史中的同指标实数事件；该断言沿初等图及历史追加保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Td_play_d (J : kpair_convention_l.Interpretation M) (c a h s : M.Domain) : Prop :=
  ∃ b, M.SuccessorOf b a ∧ ∀ i x, Rd_entry_d i x s → Tg_event_d J c i b h x

def td_play0_m : Formula 1 4 :=
  let v : Fin 4 → Term 4 := Term.bound
  set[4] ⟪∃ b, ⌜KP.succ0_m⌝ₚ(b,⌜v 1⌝ₛ) ∧ (∀ i x,
    ⌜rd_entry0_m⌝ₚ(i,x,⌜v 3⌝ₛ) → ⌜tg_event_m⌝ₚ(⌜v 0⌝ₛ,i,b,⌜v 2⌝ₛ,x))⟫

theorem td_play0_closed_l : td_play0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_play0_m,Definitional.Formula.FreeClosed]

theorem td_play0_sat_l (J : kpair_convention_l.Interpretation M) (hE : Extensional M) (ρ : Env M 4) :
    Formula.satisfies ρ td_play0_m ↔ Td_play_d J (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) := by
  simp only [td_play0_m,Td_play_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    KP.succ0_sat_l hE,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE,tg_event_sat_l J hE,Definitional.Term.eval_weaken]
  rfl

theorem Td_play_d.mono_l {J : kpair_convention_l.Interpretation M} {c a h h' s : M.Domain}
    (play : Td_play_d J c a h s) (sub : M.MemberSubset h h') : Td_play_d J c a h' s := by
  obtain ⟨b,next,events⟩ := play
  exact ⟨b,next,fun i x ix => (events i x ix).mono_l J sub⟩

def Td_play_at_d (I : kpair_convention_l.Interpretation M) (X R c a h s : M.Domain) : Prop :=
  Rr_truth_d I X R td_play0_m (fun i => [c,a,h,s].get i)

def td_play_at_m {d} (X R c a h s : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := kpair_convention_l) td_play0_m X R (fun i => [c,a,h,s].get i)

@[simp] theorem td_play_at_closed_l {d} (X R c a h s : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hc : c.freeSupport = [])
    (ha : a.freeSupport = []) (hh : h.freeSupport = []) (hs : s.freeSupport = []) :
    (td_play_at_m X R c a h s).FreeClosed := by
  apply rr_truth_closed_l td_play0_m td_play0_closed_l X R _ hX hR
  exact Fin.cases hc (Fin.cases ha (Fin.cases hh (Fin.cases hs (fun i => Fin.elim0 i))))

theorem td_play_at_sat_l (I : kpair_convention_l.Interpretation M) {d} (ρ : Env M d) (X R c a h s : Term d) :
    Formula.satisfies ρ (td_play_at_m X R c a h s) ↔
      Td_play_at_d I (X.eval ρ) (R.eval ρ) (c.eval ρ) (a.eval ρ) (h.eval ρ) (s.eval ρ) := by
  rw [td_play_at_m,rr_truth_sat_l I _ td_play0_m td_play0_closed_l]
  have eq : (fun i : Fin 4 => ([c,a,h,s].get i).eval ρ) =
      (fun i => [c.eval ρ,a.eval ρ,h.eval ρ,s.eval ρ].get i) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  exact iff_of_eq (congrArg (Rr_truth_d I (X.eval ρ) (R.eval ρ) td_play0_m) eq)

theorem td_play_native_l (I : kpair_convention_l.Interpretation M) {X R : M.Domain}
    (nx : ∃ x, M.mem x X) (hKP : (smdl_structure_l I (R := R) nx).Models KP)
    (ρ : Env (smdl_structure_l I (R := R) nx) 4) :
    Td_play_at_d I X R (ρ.bound 0).val (ρ.bound 1).val (ρ.bound 2).val (ρ.bound 3).val ↔
      Td_play_d (kp_pair_l hKP) (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) := by
  have values : (fun i => (ρ.bound i).val) =
      (fun i => [(ρ.bound 0).val,(ρ.bound 1).val,(ρ.bound 2).val,(ρ.bound 3).val].get i) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))
  change Rr_truth_d I X R td_play0_m _ ↔ _
  exact (iff_of_eq (congrArg (Rr_truth_d I X R td_play0_m) values.symm)).trans
    ((rr_truth_native_l I nx td_play0_m td_play0_closed_l ρ.bound).trans
    ((Formula.closed_env_l td_play0_m td_play0_closed_l
      (ρ := ⟨ρ.bound,fun _ => ρ.bound 0⟩) (η := ρ) rfl).trans (td_play0_sat_l (kp_pair_l hKP) hKP.1 ρ)))

theorem Td_play_at_d.mono_l (I : kpair_convention_l.Interpretation M) {cN X R c a h h' s : M.Domain}
    (model : Smdl_d I cN X R) (hKP : (smdl_structure_l I (R := R) model.2.1).Models KP)
    (play : Td_play_at_d I X R c a h s) (member : M.mem h' X)
    (sub : ∀ x, M.mem x X → M.PairMember I x h R → M.PairMember I x h' R) : Td_play_at_d I X R c a h' s := by
  let N := smdl_structure_l I (R := R) model.2.1
  let v : Fin 4 → M.Domain := fun i => [c,a,h,s].get i
  let ρ : Env N 4 := ⟨fun i => ⟨v i,play.1 i⟩,fun _ => ⟨c,play.1 0⟩⟩
  let η : Env N 4 := ⟨fun i => [ρ.bound 0,ρ.bound 1,⟨h',member⟩,ρ.bound 3].get i,ρ.free⟩
  exact (td_play_native_l I model.2.1 hKP η).mpr
    (((td_play_native_l I model.2.1 hKP ρ).mp play).mono_l (fun x hx => sub x.val x.property hx))

theorem Td_play_at_d.image_l (I : kpair_convention_l.Interpretation M) (hZF : M.Models ZF)
    {Ω cN X R cP Y S j c a h s c' a' h' : M.Domain} (hΩ : M.IsOmega Ω)
    (mx : Smdl_d I cN X R) (my : Smdl_d I cP Y S) (map : Smap_d I Ω cN cP X Y j)
    (play : Td_play_at_d I X R c a h s)
    (points : ∀ i : Fin 3, M.PairMember I ([c,a,h].get i) ([c',a',h'].get i) j) :
    ∃ t, M.PairMember I s t j ∧ Td_play_at_d I Y S c' a' h' t := by
  obtain ⟨t,_,st⟩ := map.1.1.2.2 s (play.1 3)
  exact ⟨t,st,Rr_truth_d.map_l I hZF hΩ mx my map td_play0_closed_l play
    (Fin.cases (points 0) (Fin.cases (points 1) (Fin.cases (points 2) (Fin.cases st (fun i => Fin.elim0 i)))))⟩

end YesMetaZFC.SetTheory.LargeCardinal
