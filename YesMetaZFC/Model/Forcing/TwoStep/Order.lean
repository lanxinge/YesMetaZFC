import YesMetaZFC.Model.Forcing.TwoStep.Class
import YesMetaZFC.Model.Forcing.Internal.Maximum.Pool

/-! # 地模型内的二步条件集与序关系装配 -/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Step_cond_d (B R z b W A x : M.Domain) : Prop :=
  ∃ p s, KPair_d M x p s ∧ M.mem s W ∧ Below_d M B R z p b ∧ Mem_force_d M B R z p s A

/-- 实际装配的集合与关系证书；由 `two_step_l` 同时构造。 -/
structure Two_step_d (B R z b A T W C S : M.Domain) : Prop where
  graph : ∀ v, M.mem v S → ∃ x y, KPair_d M v x y
  base : M.mem b B
  root : M.mem A W
  closed : Supp_d M B W
  conditions : ∀ x, M.mem x C ↔ Step_cond_d M B R z b W A x
  relation : ∀ x y, Entry_d M x y S ↔ M.mem x C ∧ M.mem y C ∧ Step_le_d M B R z T x y

variable {M} {B R z b A T W C S : M.Domain}

theorem two_step_mem_l (h : Two_step_d M B R z b A T W C S) {x p s} (hx : KPair_d M x p s) :
    M.mem x C ↔ M.mem s W ∧ Below_d M B R z p b ∧ Mem_force_d M B R z p s A := by
  rw [h.conditions x]
  constructor
  · rintro ⟨q, t, hq, ht, hp, hm⟩
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hx hq
    exact ⟨ht, hp, hm⟩
  · intro h
    exact ⟨p, s, hx, h⟩

theorem two_step_le_l (h : Two_step_d M B R z b A T W C S) {x y p s q t}
    (hx : M.mem x C) (hy : M.mem y C) (hxp : KPair_d M x p s) (hyq : KPair_d M y q t) :
    Entry_d M x y S ↔ Below_d M B R z p q ∧ Rel_force_d M B R z T p s t := by
  exact (h.relation x y).trans ⟨fun h => (step_le_iff_l hxp hyq).mp h.2.2,
    fun hl => ⟨hx, hy, (step_le_iff_l hxp hyq).mpr hl⟩⟩

/-- 固定名称库后，条件集和实际关系图由逐成员、逐条目方程唯一确定。 -/
theorem two_step_unique_l (hE : Extensional M) {C' S'}
    (h : Two_step_d M B R z b A T W C S) (h' : Two_step_d M B R z b A T W C' S') : C = C' ∧ S = S' := by
  have he := hE.eq_of_same_members C C' (fun x => (h.conditions x).trans (h'.conditions x).symm)
  subst C'
  exact ⟨rfl, entry_ext_l M hE h.graph h'.graph (fun x y => (h.relation x y).trans (h'.relation x y).symm)⟩

/-- 确定的混合闭库同时消除了名称库、条件集和序关系三处任意见证。 -/
theorem two_step_pool_unique_l (hE : Extensional M) {t W' C' S'}
    (hW : Name_pool_d M B A t W) (hW' : Name_pool_d M B A t W')
    (h : Two_step_d M B R z b A T W C S) (h' : Two_step_d M B R z b A T W' C' S') :
    W = W' ∧ C = C' ∧ S = S' := by
  have he := name_pool_unique_l M hE hW hW'
  subst W'
  exact ⟨rfl, two_step_unique_l hE h h'⟩

variable (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem two_step_order_l (h : Two_step_d M B R z b A T W C S)
    (hT : Name_d M B T)
    (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b) :
    Cond_order_d M C S C := by
  have hA : Name_d M B A := ⟨W, h.root, h.closed⟩
  have named x (hx : M.mem x C) : Step_named_d M B R z b A x := by
    obtain ⟨p, s, hx, hs, hp, hm⟩ := (h.conditions x).mp hx
    exact ⟨p, s, hx, ⟨W, hs, h.closed⟩, hp, hm⟩
  refine ⟨fun x hx => (h.relation x x).mpr ⟨hx, hx,
    step_named_refl_l O hZF hA hT h.base hP (named x hx)⟩, ?_, ?_⟩
  · intro x y z hx hy hz hxy hyz
    exact (h.relation x z).mpr ⟨hx, hz, step_named_trans_l O hZF hA hT h.base hP
      (named x hx) (named y hy) (named z hz) ((h.relation x y).mp hxy).2.2 ((h.relation y z).mp hyz).2.2⟩
  · intro x _ hx
    exact False.elim (KP.mem_irrefl_d (ZF.modelsKP hZF) C ((h.relation x C).mp hx).2.1)

/-- 在指定闭名称库上装配后继步，供包含顶名称的阶段嵌入复用。 -/
theorem two_step_on_l {A T b W : M.Domain} (hW : Supp_d M B W) (hAW : M.mem A W)
    (hT : Name_d M B T) (hb : M.mem b B)
    (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b) :
    ∃ C S, Two_step_d M B R z b A T W C S ∧ Cond_order_d M C S C := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push A
  let φ : BinarySchema 5 := {
    body := .conj (below_m (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 3))
      (mem_force_m (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest (.bound 2)) }
  have hφ p s : φ.denote ρ p s ↔ Below_d M B R z p b ∧ Mem_force_d M B R z p s A := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, below_sat_l M hZF.1, mem_force_sat_l M hZF.1]
    rfl
  obtain ⟨P, hP'⟩ := ZF.exists_cartesianProduct hZF I B W
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF (UnarySchema.relationMember kpair_convention_l φ) ρ P
  have hC x : M.mem x C ↔ Step_cond_d M B R z b W A x := by
    rw [hC' x, Formula.satisfies_relationMember_iff I φ ρ x, hP' x]
    constructor
    · rintro ⟨⟨p, hp, s, hs, hx⟩, q, t, hx', hφ'⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hx hx'
      exact ⟨p, s, hx, hs, (hφ p s).mp hφ'⟩
    · rintro ⟨p, s, hx, hs, hp, hm⟩
      exact ⟨⟨p, hp.1, s, hs, hx⟩, p, s, hx, (hφ p s).mpr ⟨hp, hm⟩⟩
  let η : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push T
  let ψ : BinarySchema 4 := { body := step_le_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨S, hGraph, hS⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η C
  have hr x y : Entry_d M x y S ↔ M.mem x C ∧ M.mem y C ∧ Step_le_d M B R z T x y := by
    exact (hS x y).trans (and_congr_right fun _ => and_congr_right fun _ =>
      step_le_sat_l M hZF.1 _ _ _ _ _ _ _)
  let h : Two_step_d M B R z b A T W C S := ⟨hGraph.1, hb, hAW, hW, hC, hr⟩
  exact ⟨C, S, h, two_step_order_l O hZF h hT hP⟩

/-- 后继步自动产生地模型中的条件集、序关系和预序证书；不要求地模型外部良基。 -/
theorem two_step_l {A T b : M.Domain} (hA : Name_d M B A) (hT : Name_d M B T) (hb : M.mem b B)
    (hP : Forces_d M B R z (preord_m (.bound 0) (.bound 1)) (ord_env_l M A T) b) :
    ∃ W C S, Name_pool_d M B A A W ∧ Two_step_d M B R z b A T W C S ∧ Cond_order_d M C S C := by
  obtain ⟨W, hW⟩ := name_pool_exists_l M hZF hA hA
  obtain ⟨C, S, h, L⟩ := two_step_on_l O hZF hW.closed hW.left hT hb hP
  exact ⟨W, C, S, hW, h, L⟩

end YesMetaZFC.Model.Forcing.Internal
