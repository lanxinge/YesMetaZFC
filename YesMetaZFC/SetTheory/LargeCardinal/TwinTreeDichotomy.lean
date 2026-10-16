import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCorollary610
import YesMetaZFC.SetTheory.LargeCardinal.TreeProjectionTransfer
import YesMetaZFC.SetTheory.Descriptive.GameBattle

/-! # 同一坍缩扩张中的双树二择一

6.10 与 6.7 的两个泛型分支必须在同一个名称扩张中对弈。规范名称求值的
唯一性识别两次构造的地嵌入，实际对局同时避开两树，与穷尽相矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def Td_cover_d (I : kpair_convention_l.Interpretation M) (ω A Y F T Z G S : M.Domain) : Prop :=
  ∀ x, M.IsSetFunctionFromTo I x ω A → Tp_projection_d I ω A Y F T x ∨ Tp_projection_d I ω A Z G S x

def td_cover_m {d} (ω A Y F T Z G S : Term d) : Formula 1 d := set[d] ⟪∀ x,
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(x,⌜ω⌝ₛ,⌜A⌝ₛ) →
  ⌜tp_projection_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ,⌜T⌝ₛ,x) ∨
  ⌜tp_projection_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜Z⌝ₛ,⌜G⌝ₛ,⌜S⌝ₛ,x)⟫
derive_free_closed td_cover_m

theorem td_cover_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d}
    (ρ : Env M d) (ω A Y F T Z G S : Term d) : Formula.satisfies ρ (td_cover_m ω A Y F T Z G S) ↔
    Td_cover_d I (ω.eval ρ) (A.eval ρ) (Y.eval ρ) (F.eval ρ) (T.eval ρ) (Z.eval ρ) (G.eval ρ) (S.eval ρ) := by
  simp only [td_cover_m, Td_cover_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_disj_iff,
    tp_projection_sat_l I hE, Definitional.Term.eval_weaken]; rfl

section Battle
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_battle_l {ω A Y F T Z G S : M.Domain} (hw : M.IsOmega ω)
    (cover : Td_cover_d I ω A Y F T Z G S)
    (left : Tp_win_d hZF false true ω A Y F T) (right : Tp_win_d hZF true false ω A Z G S) : False := by
  obtain ⟨H, J, B, W, τ, hist, runs, turns, payoff, win⟩ := left
  obtain ⟨H', J', B', W', σ, hist', runs', turns', payoff', win'⟩ := right
  have eqH : H' = H := hZF.1.eq_of_same_members H' H fun s => (hist' s).trans (hist s).symm
  have eqJ : J' = J := hZF.1.eq_of_same_members J' J fun n => (turns' n).trans (turns n).symm
  subst H' J'
  obtain ⟨x, fx, follows, follows'⟩ := cg_battle_l hZF hw hist win'.1 win.1
  have noT : ¬ Tp_projection_d I ω A Y F T x :=
    fun p => win.2 x ((runs x).mpr fx) follows' ((payoff x).mpr ⟨(runs x).mpr fx, p⟩)
  have noS := ((payoff' x).mp (win'.2 x ((runs' x).mpr fx) follows)).2
  exact (cover x fx).elim noT noS

end Battle
variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem td_generic_dichotomy_l {ω δ A X a Γ Y F T Λ Z G S C Q : M.Domain}
    (hw : M.IsOmega ω) (hd : Woodin_d I δ) (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A)
    (pair : M.IsCartesianProduct I Y A Γ) (space : Fseq_space_d I ω Y F) (tree : Tree_d F T)
    (pair' : M.IsCartesianProduct I Z A Λ) (space' : Fseq_space_d I ω Z G) (tree' : Tree_d G S)
    (collapse : Fseq_space_d I ω δ C)
    (order : ∀ p q, Entry_d M p q Q ↔ M.mem p C ∧ M.mem q C ∧ M.MemberSubset q p)
    (O : Cond_order_d M C Q C) {U : M.Domain → Prop} (generic : Generic_d M C Q C U)
    {p : M.Domain} (hp : U p)
    (e : M.Domain → (extension_l M hM C Q C U).Domain)
    (hi : Function.Injective e)
    (he : ∀ a y, (extension_l M hM C Q C U).mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a t, Check_d M p a t → Qval_d M C Q C U t (e a))
    (cover : Td_cover_d (kp_pair_l (ZF.modelsKP (preserves_zf_l O hM generic)))
      (e ω) (e A) (e Y) (e F) (e T) (e Z) (e G) (e S)) :
    Td_cover_d I ω A Y F T Z G S ∧
      (Tp_win_d hM true true ω A Y F T ∨ Tp_win_d hM false false ω A Z G S) := by
  let N := extension_l M hM C Q C U
  have hN : N.Models ZF := preserves_zf_l O hM generic
  have hwN := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l O hM generic) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
  refine ⟨fun x fx => ?_, ?_⟩
  · have fxN := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fx
    exact (cover (e x) fxN).imp
      (tp_projection_reflect_l hM hN e hi he hw hwN (ZFC.dc_l I hZFC hw) pair space tree fx)
      (tp_projection_reflect_l hM hN e hi he hw hwN (ZFC.dc_l I hZFC hw) pair' space' tree' fx)
  · rcases tg_corollary610_l hZFC hw hd rank hA ha pair space tree with win | win
    · exact Or.inl win
    rcases tg_corollary67_l hZFC hw hd rank hA ha pair' space' tree' with win' | win'
    · exact Or.inr win'
    have identify (f : M.Domain → N.Domain)
        (values : ∀ a t, Check_d M p a t → Qval_d M C Q C U t (f a)) : f = e := by
      funext a
      obtain ⟨t, ht, _⟩ := zf_check_l M hM (generic.proper p hp).1 a
      exact qval_unique_l (values a t ht) (hv a t ht)
    obtain ⟨f, _, _, fv, left⟩ := win C Q collapse order O U generic p hp
    obtain ⟨g, _, _, gv, right⟩ := win' C Q collapse order O U generic p hp
    have ef := identify f fv
    have eg := identify g gv
    subst f g
    exact (td_battle_l hN hwN cover left right).elim

end YesMetaZFC.SetTheory.LargeCardinal
