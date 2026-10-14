import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastStep
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePlayTrace

/-! # 全部存档的实数前缀保持在同一原历史中 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_saved_play_d (ω V q Z C c b h : M.Domain) : Prop := ∃ v : Fin 54 → M.Domain,
  Tg_saved_code_d ω V q v ∧ M.mem (v 40) Z ∧ Tg_play_d C c b h (v 40)

def tg_saved_play0_m : Formula 1 8 := rt_exists_m 54 (.conj
  (rt_tuple_m (Fin.cases (.bound 54) (Fin.cases (.bound 55) (fun i : Fin 54 => .bound (i.castAdd 8)))) (.bound 56))
  (.conj (.mem (.bound 40) (.bound 57)) (tg_play_m (.bound 58) (.bound 59) (.bound 60) (.bound 61) (.bound 40))))
theorem tg_saved_play0_closed_l : tg_saved_play0_m.FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  exact ⟨rt_tuple_closed_l _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl,
    ⟨rfl,rfl⟩, tg_play_closed_l _ _ _ _ _ rfl rfl rfl rfl rfl⟩

theorem tg_saved_play0_sat_l (hE : Extensional M) (ρ : Env M 8) : Formula.satisfies ρ tg_saved_play0_m ↔
    Tg_saved_play_d (ρ.bound 0) (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4) (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) := by
  rw [tg_saved_play0_m, rt_exists_sat_l]
  apply exists_congr
  intro v
  simp only [Formula.satisfies_conj_iff, rt_tuple_sat_l hE, tg_play_sat_l, Formula.satisfies_mem_iff, Term.eval_bound]
  have new (i : Fin 54) : (rt_push_d ρ 54 v).bound (i.castAdd 8) = v i := rt_push_new_l ρ v i
  have old (i : Fin 8) : (rt_push_d ρ 54 v).bound (Fin.natAdd 54 i) = ρ.bound i := rt_push_old_l ρ v i
  have tuple : (fun i : Fin 56 => ((Fin.cases (.bound 54) (Fin.cases (.bound 55)
      (fun j : Fin 54 => .bound (j.castAdd 8))) i : Term 62).eval (rt_push_d ρ 54 v))) =
      Fin.cases (ρ.bound 0) (Fin.cases (ρ.bound 1) v) := by
    funext i
    exact Fin.cases (old 0) (Fin.cases (old 1) new) i
  rw [tuple, show (rt_push_d ρ 54 v).bound 56 = ρ.bound 2 from old 2,
    show (rt_push_d ρ 54 v).bound 57 = ρ.bound 3 from old 3,
    show (rt_push_d ρ 54 v).bound 58 = ρ.bound 4 from old 4,
    show (rt_push_d ρ 54 v).bound 59 = ρ.bound 5 from old 5,
    show (rt_push_d ρ 54 v).bound 60 = ρ.bound 6 from old 6,
    show (rt_push_d ρ 54 v).bound 61 = ρ.bound 7 from old 7,
    show (rt_push_d ρ 54 v).bound 40 = v 40 from new 40]
  rfl

def tg_saved_play_m {d} (ω V q Z C c b h : Term d) : Formula 1 d :=
  tg_saved_play0_m.bind (fun i => [ω,V,q,Z,C,c,b,h].get i)
@[simp] theorem tg_saved_play_closed_l {d} (v : Fin 8 → Term d) (hv : ∀ i, (v i).freeSupport = []) :
    (tg_saved_play0_m.bind v).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ hv _).mpr tg_saved_play0_closed_l
theorem tg_saved_play_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω V q Z C c b h : Term d) :
    Formula.satisfies ρ (tg_saved_play_m ω V q Z C c b h) ↔
      Tg_saved_play_d (ω.eval ρ) (V.eval ρ) (q.eval ρ) (Z.eval ρ) (C.eval ρ) (c.eval ρ) (b.eval ρ) (h.eval ρ) := by
  rw [tg_saved_play_m, Formula.satisfies_bind, tg_saved_play0_sat_l hE]; rfl

def Tg_past_play_d (ω H Z C c b h : M.Domain) : Prop := ∀ m i Y R μ K η D L V q,
  Tg_past_at_d H m i Y R μ K η D L V q → Tg_saved_play_d ω V q Z C c b h
def tg_past_play_m {d} (ω H Z C c b h : Term d) : Formula 1 d := set[d] ⟪∀ m i Y R μ K η D L V q,
  ⌜tg_past_at_m⌝ₚ(⌜H⌝ₛ,m,i,Y,R,μ,K,η,D,L,V,q) → ⌜tg_saved_play_m⌝ₚ(⌜ω⌝ₛ,V,q,⌜Z⌝ₛ,⌜C⌝ₛ,⌜c⌝ₛ,⌜b⌝ₛ,⌜h⌝ₛ)⟫
@[simp] theorem tg_past_play_closed_l {d} (ω H Z C c b h : Term d)
    (hw : ω.freeSupport = []) (hH : H.freeSupport = []) (hZ : Z.freeSupport = []) (hC : C.freeSupport = [])
    (hc : c.freeSupport = []) (hb : b.freeSupport = []) (hh : h.freeSupport = []) : (tg_past_play_m ω H Z C c b h).FreeClosed := by
  simp -implicitDefEqProofs [tg_past_play_m, tg_saved_play_m, Definitional.Formula.FreeClosed, hw, hH, hZ, hC, hc, hb, hh,
    Fin.forall_fin_succ, tg_saved_play0_closed_l]
theorem tg_past_play_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H Z C c b h : Term d) :
    Formula.satisfies ρ (tg_past_play_m ω H Z C c b h) ↔
      Tg_past_play_d (ω.eval ρ) (H.eval ρ) (Z.eval ρ) (C.eval ρ) (c.eval ρ) (b.eval ρ) (h.eval ρ) := by
  simp only [tg_past_play_m, Tg_past_play_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    tg_past_at_sat_l hE, tg_saved_play_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem tg_past_play_empty_l {ω H Z C c b h : M.Domain} (empty : ∀ x, ¬ M.mem x H) : Tg_past_play_d ω H Z C c b h :=
  fun _ _ _ _ _ _ _ _ _ _ _ ⟨_, ⟨p, _, hp⟩, _⟩ => (empty p hp).elim

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

theorem Tg_past_play_d.mono_l {ω H Z C : M.Domain} (ct : M.TransitiveSet C) (nc : Nonempty {x // M.mem x C})
    (J : kpair_convention_l.Interpretation (rt_model_l C nc)) (c b h h' : (rt_model_l C nc).Domain)
    (play : Tg_past_play_d ω H Z C c.val b.val h.val) (sub : M.MemberSubset h.val h'.val) :
    Tg_past_play_d ω H Z C c.val b.val h'.val := by
  intro m i Y R μ K η D L V q row
  obtain ⟨v, code, low, play⟩ := play m i Y R μ K η D L V q row
  exact ⟨v, code, low, play.mono_l hZF ct nc J c b h h' sub⟩

theorem Tg_past_play_d.map_l {ω H Z X R d Y S e j C C' c c' b b' h h' : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I d X R) (my : Smem_d I e Y S) (map : Smap_d I ω d e X Y j)
    (iC : Rd_entry_d C C' j) (ic : Rd_entry_d c c' j) (ib : Rd_entry_d b b' j) (ih : Rd_entry_d h h' j)
    (fixed : ∀ s, M.mem s Z → Rd_entry_d s s j) (play : Tg_past_play_d ω H Z C c b h) : Tg_past_play_d ω H Z C' c' b' h' := by
  intro m i U T μ K η D L V q row
  obtain ⟨v, code, low, play⟩ := play m i U T μ K η D L V q row
  exact ⟨v, code, low, play.map_l hZF hw xt yt mx my map iC ic ib ih (fixed _ low)⟩

theorem Tg_past_play_d.push_l {ω n H n' H' X b Z C c d h i Y R μ K η D L V q : M.Domain}
    (updated : Tg_past_d hZF ω n' H' X b) (succ : M.SuccessorOf n' n)
    (newest : Tg_past_at_d H' n i Y R μ K η D L V q)
    (entries : ∀ m r, M.mem m n → (Rd_entry_d m r H' ↔ Rd_entry_d m r H))
    (play : Tg_past_play_d ω H Z C c d h) (v : Fin 54 → M.Domain) (code : Tg_saved_code_d ω V q v)
    (low : M.mem (v 40) Z) (trace : Tg_play_d C c d h (v 40)) : Tg_past_play_d ω H' Z C c d h := by
  intro m i₀ Y₀ R₀ μ₀ K₀ η₀ D₀ L₀ V₀ q₀ row
  obtain ⟨r, hr, cell⟩ := row
  rcases (succ m).mp ((updated.sequence.2.2 m).mpr ⟨r, hr⟩) with lt | eq
  · exact play m i₀ Y₀ R₀ μ₀ K₀ η₀ D₀ L₀ V₀ q₀ ⟨r, (entries m r lt).mp hr, cell⟩
  · have eq := hZF.1.eq_of_same_members m n eq
    subst m
    obtain ⟨s, hs, pack⟩ := newest
    have eq := updated.sequence.2.1.2 n r s hr hs
    subst s
    have eq := rt_tuple_inj_l cell pack
    have eV : V₀ = V := congrFun eq 8
    have eq : q₀ = q := congrFun eq 9
    subst V₀ q₀
    exact ⟨v, code, low, trace⟩

end YesMetaZFC.SetTheory.LargeCardinal
