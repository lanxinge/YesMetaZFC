import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawExactHistory
import YesMetaZFC.Model.SetTheory.Relations.RankImage
import YesMetaZFC.Model.SetTheory.Relations.NativeRank
import YesMetaZFC.Model.SetTheory.Relations.CrossCapture
import YesMetaZFC.SetTheory.CumulativeComparison
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.InitialPull
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.Card.Cofinality.OmegaAddition
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis

/-! # 原生复制历史中的共同秩段

两个秩高保留各自所属模型的对象码。共同层由实际完整前驱图给出，
端点只要求全部成员的实现，不错误地要求支撑高度属于自身的秩段。
较高共同层延伸这份记录时，原层、复合图及全局缺失见证一同保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Ic_common_d (I : kpair_convention_l.Interpretation M)
    (X R N S L l U V D t : M.Domain) : Prop where
  left_rank : Rr_rank_d I X R L U
  right_rank : Rr_rank_d I N S l V
  limit : Rr_truth_d I X R (Formula.isLimitOrdinal .newest) (fun _ : Fin 1 => L)
  carrier : ∀ x, M.mem x D ↔ M.mem x X ∧ Rd_entry_d x U R
  injection : M.IsSetInjectionFromTo I t D N
  image : ∀ E, Rd_entry_d E V S ↔ ∃ x, M.mem x D ∧ Rd_entry_d x E t
  pred : ∀ x E, Rd_entry_d x E t → ∀ P,
    Rd_entry_d P E S ↔ ∃ y, Rd_entry_d y x R ∧ Rd_entry_d y P t
  left_closed : Rr_closed_d I X R U
  right_closed : Rr_closed_d I N S V
  endpoint : Er_rep_d X R N S t L l
  exactness : Er_exact_d X R N S L t

/-! 共同秩段的 `Rr_rank_d` 已经把两端秩对象作为所属模型成员记录。
单独命名这两个投影，后续历史运输可直接取得高辅助对象的源端归属，
无需重新展开秩公式。 -/
theorem Ic_common_d.left_rank_mem_l
    {X R N S L l U V D t : M.Domain}
    (h : Ic_common_d I X R N S L l U V D t) :
    M.mem U X := by
  obtain ⟨_, hU, _⟩ := h.left_rank
  exact hU

theorem Ic_common_d.right_rank_mem_l
    {X R N S L l U V D t : M.Domain}
    (h : Ic_common_d I X R N S L l U V D t) :
    M.mem V N := by
  obtain ⟨_, hV, _⟩ := h.right_rank
  exact hV

private def ic_common_graph_m {d} (X R N S L l U V D t : Term d) : Formula 1 d := set[d] ⟪
  (∀ x, x ∈ ⌜D⌝ₛ ↔ x ∈ ⌜X⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(x, ⌜U⌝ₛ, ⌜R⌝ₛ)) ∧
  ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(⌜t⌝ₛ, ⌜D⌝ₛ, ⌜N⌝ₛ) ∧
  (∀ E, ⌜rd_entry0_m⌝ₚ(E, ⌜V⌝ₛ, ⌜S⌝ₛ) ↔ ∃ x ∈ ⌜D⌝ₛ, ⌜rd_entry0_m⌝ₚ(x, E, ⌜t⌝ₛ)) ∧
  (∀ x E, ⌜rd_entry0_m⌝ₚ(x, E, ⌜t⌝ₛ) → ∀ P,
    ⌜rd_entry0_m⌝ₚ(P, E, ⌜S⌝ₛ) ↔ ∃ y, ⌜rd_entry0_m⌝ₚ(y, x, ⌜R⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(y, P, ⌜t⌝ₛ)) ∧
  (∀ a b, a ∈ ⌜X⌝ₛ → b ∈ ⌜X⌝ₛ → ⌜rd_entry0_m⌝ₚ(a, ⌜U⌝ₛ, ⌜R⌝ₛ) →
    (∀ x ∈ ⌜X⌝ₛ, ⌜rd_entry0_m⌝ₚ(x, b, ⌜R⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x, a, ⌜R⌝ₛ)) →
      ⌜rd_entry0_m⌝ₚ(b, ⌜U⌝ₛ, ⌜R⌝ₛ)) ∧
  (∀ a b, a ∈ ⌜N⌝ₛ → b ∈ ⌜N⌝ₛ → ⌜rd_entry0_m⌝ₚ(a, ⌜V⌝ₛ, ⌜S⌝ₛ) →
    (∀ x ∈ ⌜N⌝ₛ, ⌜rd_entry0_m⌝ₚ(x, b, ⌜S⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x, a, ⌜S⌝ₛ)) →
      ⌜rd_entry0_m⌝ₚ(b, ⌜V⌝ₛ, ⌜S⌝ₛ)) ∧
  ⌜er_rep_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜N⌝ₛ, ⌜S⌝ₛ, ⌜t⌝ₛ, ⌜L⌝ₛ, ⌜l⌝ₛ) ∧
  ⌜er_exact_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜N⌝ₛ, ⌜S⌝ₛ, ⌜L⌝ₛ, ⌜t⌝ₛ)⟫
derive_free_closed ic_common_graph_m

def ic_common_m {d} (X R N S L l U V D t : Term d) : Formula 1 d :=
  .conj (rr_rank_m X R L U) (.conj (rr_rank_m N S l V)
    (.conj (rr_truth_m (𝒞 := kpair_convention_l) (Formula.isLimitOrdinal .newest) X R (fun _ : Fin 1 => L))
      (ic_common_graph_m X R N S L l U V D t)))

@[simp] theorem ic_common_closed_l {d} (X R N S L l U V D t : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hN : N.freeSupport = []) (hS : S.freeSupport = [])
    (hL : L.freeSupport = []) (hl : l.freeSupport = []) (hU : U.freeSupport = []) (hV : V.freeSupport = [])
    (hD : D.freeSupport = []) (ht : t.freeSupport = []) : (ic_common_m X R N S L l U V D t).FreeClosed := by
  refine ⟨rr_rank_closed_l X R L U hX hR hL hU, rr_rank_closed_l N S l V hN hS hl hV,
    rr_truth_closed_l _ (by simp -implicitDefEqProofs) X R _ hX hR (fun _ => hL), ?_⟩
  simp -implicitDefEqProofs [hX, hR, hN, hS, hL, hl, hU, hV, hD, ht]

theorem ic_common_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (X R N S L l U V D t : Term d) :
    Formula.satisfies ρ (ic_common_m X R N S L l U V D t) ↔
      Ic_common_d (kp_pair_l hKP) (X.eval ρ) (R.eval ρ) (N.eval ρ) (S.eval ρ) (L.eval ρ) (l.eval ρ)
        (U.eval ρ) (V.eval ρ) (D.eval ρ) (t.eval ρ) := by
  simp only [ic_common_m, ic_common_graph_m, Formula.satisfies_conj_iff, rr_rank_sat_l (kp_pair_l hKP),
    rr_truth_sat_l (kp_pair_l hKP) ρ (Formula.isLimitOrdinal (.newest : Term 1)) (by simp -implicitDefEqProofs),
    Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1, er_rep_sat_l hKP.1, er_exact_sat_l hKP.1,
    Formula.satisfies_isInjectionFromTo_iff (kp_pair_l hKP) hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
    fun h => ⟨h.left_rank, h.right_rank, h.limit, h.carrier, h.injection, h.image, h.pred,
      h.left_closed, h.right_closed, h.endpoint, h.exactness⟩⟩

/-- 原共同层和两个工作秩段由同一对复制图对应，包含端点及秩对象的实际像。 -/
structure Ic_agree_d (I : kpair_convention_l.Interpretation M)
    (X R A π N S B σ L l φ U V D t : M.Domain) : Prop where
  common : Ic_common_d I X R N S L l U V D t
  left_trans : M.TransitiveSet A
  right_trans : M.TransitiveSet B
  limit : M.IsLimitOrdinal φ
  work : ∃ W, M.mem W A ∧ M.mem W B ∧ Vr_d A φ W ∧ Vr_d B φ W ∧
    Rd_entry_d U W π ∧ Rd_entry_d V W σ
  left_end : Rd_entry_d L φ π
  right_end : Rd_entry_d l φ σ
  points : ∀ x x' E, Rd_entry_d x x' π → Rd_entry_d x E t → Rd_entry_d E x' σ

def ic_agree_m {d} (X R A π N S B σ L l φ U V D t : Term d) : Formula 1 d := set[d] ⟪
  ⌜ic_common_m⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜N⌝ₛ, ⌜S⌝ₛ, ⌜L⌝ₛ, ⌜l⌝ₛ, ⌜U⌝ₛ, ⌜V⌝ₛ, ⌜D⌝ₛ, ⌜t⌝ₛ) ∧
  ⌜Formula.isTransitive⌝ₚ(⌜A⌝ₛ) ∧ ⌜Formula.isTransitive⌝ₚ(⌜B⌝ₛ) ∧ ⌜Formula.isLimitOrdinal⌝ₚ(⌜φ⌝ₛ) ∧
  (∃ W, W ∈ ⌜A⌝ₛ ∧ W ∈ ⌜B⌝ₛ ∧ ⌜pn_rank_m⌝ₚ(⌜A⌝ₛ, ⌜φ⌝ₛ, W) ∧ ⌜pn_rank_m⌝ₚ(⌜B⌝ₛ, ⌜φ⌝ₛ, W) ∧
    ⌜rd_entry0_m⌝ₚ(⌜U⌝ₛ, W, ⌜π⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜V⌝ₛ, W, ⌜σ⌝ₛ)) ∧
  ⌜rd_entry0_m⌝ₚ(⌜L⌝ₛ, ⌜φ⌝ₛ, ⌜π⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜φ⌝ₛ, ⌜σ⌝ₛ) ∧
  (∀ x x' E, ⌜rd_entry0_m⌝ₚ(x, x', ⌜π⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x, E, ⌜t⌝ₛ) → ⌜rd_entry0_m⌝ₚ(E, x', ⌜σ⌝ₛ))⟫
derive_free_closed ic_agree_m

theorem ic_agree_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (X R A π N S B σ L l φ U V D t : Term d) :
    Formula.satisfies ρ (ic_agree_m X R A π N S B σ L l φ U V D t) ↔
      Ic_agree_d (kp_pair_l hKP) (X.eval ρ) (R.eval ρ) (A.eval ρ) (π.eval ρ) (N.eval ρ) (S.eval ρ)
        (B.eval ρ) (σ.eval ρ) (L.eval ρ) (l.eval ρ) (φ.eval ρ) (U.eval ρ) (V.eval ρ) (D.eval ρ) (t.eval ρ) := by
  simp only [ic_agree_m, Formula.satisfies_conj_iff, ic_common_sat_l hKP,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_mem_iff, pn_rank_sat_l hKP, rd_entry0_sat_l hKP.1,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨a, b, c, d, e, f, g, h⟩,
    fun h => ⟨h.common, h.left_trans, h.right_trans, h.limit, h.work, h.left_end, h.right_end, h.points⟩⟩

/-- 源端极限的全部成员实现为目标端点，因此目标仍是非零无顶的极限序数。 -/
theorem Ic_common_d.right_limit_native_l (I : kpair_convention_l.Interpretation M)
    {X R Y S L l U V Γ g c d : M.Domain}
    (hE : Extensional M) (common : Ic_common_d I X R Y S L l U V Γ g)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP) :
    (smdl_structure_l I (R := S) my.2.1).IsLimitOrdinal ⟨l,common.right_rank.1⟩ := by
  have eq : I.Codes = KPair_d M := by
    funext p x y
    let ρ : Env M 3 := ⟨fun i => [p,x,y].get i,fun _ => p⟩
    exact propext ((I.realizes ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      (kpair_sat_l M hE ρ (.bound 0) (.bound 1) (.bound 2)))
  rcases I with ⟨codes,realizes,total,unique,injective⟩
  change codes = KPair_d M at eq
  subst codes
  let I : kpair_convention_l.Interpretation M := ⟨KPair_d M,realizes,total,unique,injective⟩
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Yn := smdl_structure_l I (R := S) my.2.1
  let Ln : Xn.Domain := ⟨L,common.left_rank.1⟩
  let Un : Xn.Domain := ⟨U,common.left_rank.2.1⟩
  have left : Xn.IsLimitOrdinal Ln := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mx.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => Ln)).mp common.limit)
  have rank : V_d (kp_pair_l hX) Ln Un := (rr_rank_native_l I mx.2.1 hX Ln Un).mp common.left_rank
  have right := (rr_rank_native_l I my.2.1 hY
    (⟨l,common.right_rank.1⟩ : Yn.Domain) ⟨V,common.right_rank.2.1⟩).mp common.right_rank
  have pick (x : Xn.Domain) (hx : Xn.mem x Ln) : ∃ y : Yn.Domain,
      Rd_entry_d x.val y.val g ∧ Rd_entry_d y.val l S := by
    have hu := KP.v_ordinal_subset_l hX rank x hx
    obtain ⟨y,hy,xy⟩ := common.injection.1.2.2 x.val ((common.carrier x.val).mpr ⟨x.property,hu⟩)
    exact ⟨⟨y,hy⟩,xy,(common.endpoint.2.2 y).mpr ⟨x.val,x.property,hx,xy⟩⟩
  obtain ⟨a,ha⟩ := left.2.1
  obtain ⟨a',_,ha'⟩ := pick a ha
  refine ⟨v_ordinal_l (kp_pair_l hY) right,⟨a',ha'⟩,?_⟩
  intro y hy
  obtain ⟨x,hx,xL,xy⟩ := (common.endpoint.2.2 y.val).mp hy
  obtain ⟨b,bL,xb⟩ := left.2.2 ⟨x,hx⟩ xL
  obtain ⟨b',bb,b'l⟩ := pick b bL
  exact ⟨b',b'l,(common.pred b.val b'.val bb y.val).mpr ⟨x,xb,xy⟩⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 共同端点的完整极限性由实际工作像读取，不要求原模型满足 KP。 -/
theorem Ic_agree_d.right_limit_l
    {ω X R A π N S B σ L l φ U V D t cn cb RB : M.Domain}
    (a : Ic_agree_d I X R A π N S B σ L l φ U V D t)
    (hω : M.IsOmega ω) (mn : Smdl_d I cn N S) (mb : Smem_d I cb B RB)
    (map : Smap_d I ω cn cb N B σ) :
    Rr_truth_d I N S (KP.limit0_m .newest) (fun _ : Fin 1 => l) := by
  have h := (rr_truth_mem_l I a.right_trans mb (KP.limit0_m .newest) (KP.limit0_delta_l _)
    (fun _ : Fin 1 => φ)).mpr ⟨fun _ => map.1.1.output_mem_of_pairMember a.right_end,
      (KP.limit0_sat_l (ZF.modelsKP hZF) _ .newest).mpr a.limit⟩
  exact h.pull_l I hZF hω mn mb.1 map (by simp -implicitDefEqProofs) (fun _ => a.right_end)

/-- 高度比较只读取上述完整极限事实中的序数部分。 -/
theorem Ic_agree_d.right_ord_l
    {ω X R A π N S B σ L l φ U V D t cn cb RB : M.Domain}
    (a : Ic_agree_d I X R A π N S B σ L l φ U V D t)
    (hω : M.IsOmega ω) (mn : Smdl_d I cn N S) (mb : Smem_d I cb B RB)
    (map : Smap_d I ω cn cb N B σ) :
    Rr_truth_d I N S (KP.ord0_m .newest) (fun _ : Fin 1 => l) := by
  obtain ⟨m, h⟩ := a.right_limit_l hZF hω mn mb map
  exact ⟨m, ((Formula.satisfies_conj_iff ..).mp h).1⟩

/-- 两个共同层通过已有切片秩历史复合，且保留同一个实际复合图。 -/
theorem Ic_common_d.trans_l {X R N S C W L l U V D t μ ν A B E s c d : M.Domain}
    (a : Ic_common_d I X R N S L l U V D t)
    (b : Ic_common_d I N S C W μ ν A B E s)
    (mn : Smdl_d I c N S) (mc : Smdl_d I d C W)
    (ext : Extensional (smdl_structure_l I (R := W) mc.2.1))
    (trans : Rr_truth_d I N S (Formula.isTransitive .newest) (fun _ : Fin 1 => A))
    (hlA : Rd_entry_d l A S) (hVA : Rd_entry_d V A S)
    (rank : Rr_truth_d I N S (pn_rank_m (.bound 2) (.bound 1) .newest)
      (Fin.cases V (Fin.cases l (fun _ : Fin 1 => A)))) :
    ∃ l' V' v, Rd_entry_d l l' s ∧ Rd_entry_d V V' s ∧ It_comp_d t s v ∧
      Ic_common_d I X R C W L l' U V' D v := by
  let N₀ := smdl_structure_l I (R := S) mn.2.1
  let A₀ : N₀.Domain := ⟨A, b.left_rank.2.1⟩
  let l₀ : N₀.Domain := ⟨l, a.right_rank.1⟩
  let V₀ : N₀.Domain := ⟨V, a.right_rank.2.1⟩
  have ta : N₀.TransitiveSet A₀ := (Formula.satisfies_isTransitive_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isTransitive .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => A₀)).mp trans)
  have hlE := (b.carrier l).mpr ⟨l₀.property, hlA⟩
  have hVE := (b.carrier V).mpr ⟨V₀.property, hVA⟩
  obtain ⟨l', _, hll⟩ := b.injection.1.2.2 l hlE
  obtain ⟨V', _, hVV⟩ := b.injection.1.2.2 V hVE
  have down x y (hx : M.mem x E) (hyx : Rd_entry_d y x S) : M.mem y E :=
    (b.carrier y).mpr ⟨(mn.2.2.2 y x hyx).1,
      ta ⟨x, ((b.carrier x).mp hx).1⟩ ((b.carrier x).mp hx).2
        ⟨y, (mn.2.2.2 y x hyx).1⟩ hyx⟩
  have inside x y (hxy : Rd_entry_d x y t) : M.mem y E :=
    (b.carrier y).mpr ⟨a.injection.1.output_mem_of_pairMember hxy,
      ta V₀ hVA ⟨y, a.injection.1.output_mem_of_pairMember hxy⟩
        ((a.image y).mpr ⟨x, a.injection.1.input_mem_of_pairMember hxy, hxy⟩)⟩
  have ft := fn0_function_l (ZF.modelsKP hZF)
    ((fn0_of_function_l (ZF.modelsKP hZF) a.injection.1).retarget_l inside)
  obtain ⟨v, fv, graph⟩ := ZF.exists_compositionFunction hZF I ft b.injection.1
  have comp : It_comp_d t s v := ⟨fv.1.1, fun x y => (graph x y).trans
    ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨a.injection.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩
  have inj : M.IsSetInjectionFromTo I v D C := by
    refine ⟨fv, fun x y P hx hy => ?_⟩
    obtain ⟨E₀, hxE, hEP⟩ := (comp.2 x P).mp hx
    obtain ⟨F₀, hyF, hFP⟩ := (comp.2 y P).mp hy
    exact a.injection.2 x y F₀ (b.injection.2 E₀ F₀ P hEP hFP ▸ hxE) hyF
  have image P : Rd_entry_d P V' W ↔ ∃ x, M.mem x D ∧ Rd_entry_d x P v := by
    constructor
    · intro hP
      obtain ⟨Q, hQV, hQP⟩ := (b.pred V V' hVV P).mp hP
      obtain ⟨x, hx, hxQ⟩ := (a.image Q).mp hQV
      exact ⟨x, hx, (comp.2 x P).mpr ⟨Q, hxQ, hQP⟩⟩
    · rintro ⟨x, hx, hxP⟩
      obtain ⟨Q, hxQ, hQP⟩ := (comp.2 x P).mp hxP
      exact (b.pred V V' hVV P).mpr ⟨Q, (a.image Q).mpr ⟨x, hx, hxQ⟩, hQP⟩
  have pred x P (hxP : Rd_entry_d x P v) Q :
      Rd_entry_d Q P W ↔ ∃ y, Rd_entry_d y x R ∧ Rd_entry_d y Q v := by
    obtain ⟨E₀, hxE, hEP⟩ := (comp.2 x P).mp hxP
    constructor
    · intro hQP
      obtain ⟨F₀, hFE, hFQ⟩ := (b.pred E₀ P hEP Q).mp hQP
      obtain ⟨y, hyx, hyF⟩ := (a.pred x E₀ hxE F₀).mp hFE
      exact ⟨y, hyx, (comp.2 y Q).mpr ⟨F₀, hyF, hFQ⟩⟩
    · rintro ⟨y, hyx, hyQ⟩
      obtain ⟨F₀, hyF, hFQ⟩ := (comp.2 y Q).mp hyQ
      exact (b.pred E₀ P hEP Q).mpr ⟨F₀, (a.pred x E₀ hxE F₀).mpr ⟨y, hyx, hyF⟩, hFQ⟩
  -- 直接使用较高切片内的实际历史，不把局部秩比较加强为整个原模型的 KP。
  let p : Fin 3 → N₀.Domain := fun i =>
    ⟨Fin.cases V (Fin.cases l (fun _ : Fin 1 => A)) i,
      Fin.cases a.right_rank.2.1 (Fin.cases a.right_rank.1 (fun _ => b.left_rank.2.1)) i⟩
  have history := (rr_truth_native_l I mn.2.1 (pn_rank_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) p).mp rank
  simp only [pn_rank_m, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Definitional.Term.eval_weaken] at history
  let na : Nonempty {x : N₀.Domain // N₀.mem x A₀} := ⟨⟨l₀, hlA⟩⟩
  have localRank : Formula.satisfies
      (⟨Fin.cases ⟨V₀, hVA⟩ (fun _ => ⟨l₀, hlA⟩), fun _ => ⟨l₀, hlA⟩⟩ : Env (rt_model_l A₀ na) 2)
      (v_sigma_m (.bound 1) .newest) := by
    obtain ⟨D₁, hD₁, F₁, hF₁, cert⟩ := history
    refine ⟨⟨D₁, hD₁⟩, ⟨F₁, hF₁⟩, fun x => ?_⟩
    exact (rt_model_delta_l ta na (vc_matrix_delta_l ..) _).mpr (cert x.val x.property)
  have target := rr_native_rank_value_l I mn.2.1 mc.2.1 ext
    A₀ l₀ V₀ ta b.carrier b.injection b.image b.pred b.right_closed hlA hVA hll hVV localRank
  have closed := rr_cross_closed_l I mn.2.1 A₀ V₀ ta b.carrier b.injection b.image b.pred
    b.right_closed hVV a.right_closed
  have endpoint := (er_rep_comp_l (ZF.modelsKP hZF) b.injection
    (fun x hx => ((b.carrier x).mp hx).1) down inside b.pred comp hll).mp a.endpoint
  let nx : ∃ x, M.mem x X := ⟨L, a.left_rank.1⟩
  let L₀ : (smdl_structure_l I (R := R) nx).Domain := ⟨L, a.left_rank.1⟩
  have limitX := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I nx (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => L₀)).mp a.limit)
  have exactness := a.exactness.comp_l (ZF.modelsKP hZF) b.injection b.carrier down inside b.image b.pred
    b.left_closed b.right_closed comp hlE a.endpoint
    (fun x y hx hy hxl hyx => limitX.1.transitive ⟨x, hx⟩ hxl ⟨y, hy⟩ hyx)
  exact ⟨l', V', v, hll, hVV, comp,
    ⟨a.left_rank, target, a.limit, a.carrier, inj, image, pred,
      a.left_closed, closed, endpoint, exactness⟩⟩

/-- 严格较早的原生共同层沿下一层延伸；工作秩段和逐点方块同步复合。 -/
theorem Ic_agree_d.trans_l
    {ω X R A π N S B σ C T D τ L l φ U V E t μ ν ψ H J F s cn cc cb RB : M.Domain}
    (a : Ic_agree_d I X R A π N S B σ L l φ U V E t)
    (b : Ic_agree_d I N S B σ C T D τ μ ν ψ H J F s)
    (hω : M.IsOmega ω) (mn : Smdl_d I cn N S) (mc : Smdl_d I cc C T) (mb : Smem_d I cb B RB)
    (map : Smap_d I ω cn cb N B σ)
    (ext : Extensional (smdl_structure_l I (R := T) mc.2.1)) (lt : Rd_entry_d l μ S) :
    ∃ l' V' v, Rd_entry_d l l' s ∧ Rd_entry_d V V' s ∧ It_comp_d t s v ∧
      Ic_agree_d I X R A π C T D τ L l' φ U V' E v := by
  have lt' := ((mb.2 φ ψ).mp ((map.relation_l I hZF hω mn mb.1 a.right_end b.left_end).mp lt)).2.2
  obtain ⟨W, hwA, hwB, rwA, rwB, huW, hvW⟩ := a.work
  obtain ⟨Z, hzB, hzD, rzB, rzD, hHZ, _⟩ := b.work
  have hφZ := rzB.ordinal_subset_l hZF b.left_trans hzB φ lt'
  obtain ⟨hwZ, rwZ⟩ := rzB.rank_l hZF b.left_trans hzB b.limit hφZ hwB rwB
  have pull_mem {x y x' y'} (hx : Rd_entry_d x x' σ) (hy : Rd_entry_d y y' σ) (h : M.mem x' y') :
      Rd_entry_d x y S := (map.relation_l I hZF hω mn mb.1 hx hy).mpr
    ((mb.2 x' y').mpr ⟨map.1.1.output_mem_of_pairMember hx, map.1.1.output_mem_of_pairMember hy, h⟩)
  have trans := (rr_truth_mem_l I b.left_trans mb (Formula.isTransitive .newest)
    (Formula.isTransitive_delta0 _) (fun _ : Fin 1 => Z)).mpr
      ⟨fun _ => hzB, (Formula.satisfies_isTransitive_iff ..).mpr (rzB.transitive_l b.left_trans hzB)⟩
  have trans := trans.pull_l I hZF hω mn mb.1 map (by simp -implicitDefEqProofs) (fun _ => hHZ)
  let p : Fin 3 → M.Domain := Fin.cases W (Fin.cases φ (fun _ => Z))
  let q : Fin 3 → M.Domain := Fin.cases V (Fin.cases l (fun _ => H))
  have members : ∀ i, M.mem (p i) B :=
    Fin.cases hwB (Fin.cases (map.1.1.output_mem_of_pairMember a.right_end) (fun _ => hzB))
  have images : ∀ i, Rd_entry_d (q i) (p i) σ := Fin.cases hvW (Fin.cases a.right_end (fun _ => hHZ))
  have rank : Rr_truth_d I B RB (pn_rank_m (.bound 2) (.bound 1) .newest) p :=
    (rr_truth_mem_l I b.left_trans mb (pn_rank_m (.bound 2) (.bound 1) .newest)
    (.existsMem _ (.existsMem _ (.forallMem _ (vc_matrix_delta_l ..))))
    p).mpr ⟨members, (pn_rank_sat_l (ZF.modelsKP hZF) (⟨p, fun _ => W⟩ : Env M 3)
      (.bound 2) (.bound 1) .newest).mpr rwZ⟩
  have rank := rank.pull_l I hZF hω mn mb.1 map (by simp -implicitDefEqProofs)
    images
  obtain ⟨l', V', v, hll, hVV, comp, common⟩ := a.common.trans_l hZF b.common mn mc ext trans
    (pull_mem a.right_end hHZ hφZ) (pull_mem hvW hHZ hwZ) rank
  have hwD := b.right_trans Z hzD W hwZ
  have rwD := rzD.of_rank_l b.right_trans hzD hwZ rwZ
  refine ⟨l', V', v, hll, hVV, comp, common, a.left_trans, b.right_trans, a.limit,
    ⟨W, hwA, hwD, rwA, rwD, huW, b.points V W V' hvW hVV⟩, a.left_end,
    b.points l φ l' a.right_end hll, ?_⟩
  intro x x' E hxx hxE
  obtain ⟨y, hxy, hyE⟩ := (comp.2 x E).mp hxE
  exact b.points y x' E (a.points x x' y hxx hxy) hyE

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 活动边沿低秩方块搬运档案共同层 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 原边在临界点以下搬运每份旧档案，同时保留其实际工作解释。 -/
def Ic_archive_image_d (I : kpair_convention_l.Interpretation M)
    (N R B σ Y S D τ j κ : M.Domain) : Prop :=
  ∀ X T A π L l φ U V Γ g,
    Ic_agree_d I X T A π N R B σ L l φ U V Γ g → Rd_entry_d l κ R →
      ∃ l' V' g', Ic_agree_d I X T A π Y S D τ L l' φ U V' Γ g' ∧
        ∀ x y E, Rd_entry_d x y g → (Rd_entry_d x E g' ↔ Rd_entry_d y E j)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 一条活动边的共同层复合，在低秩方块上与同一原树边逐点相等。 -/
theorem Ic_agree_d.archive_step_l
    {ω N R B σ P S C τ μ ν ψ U V Γ t c d a RB j : M.Domain}
    (step : Ic_agree_d I N R B σ P S C τ μ ν ψ U V Γ t)
    (hω : M.IsOmega ω) (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (mb : Smem_d I a B RB) (map : Smap_d I ω c a N B σ)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (ext : Extensional (smdl_structure_l I (R := S) mp.2.1))
    (κ K : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (rank : V_d (kp_pair_l hN) κ K) (below : Rd_entry_d κ.val μ R)
    (square : ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x K → ∀ E,
        Rd_entry_d x.val E t ↔ Rd_entry_d x.val E j) :
    Ic_archive_image_d I N R B σ P S C τ j κ.val := by
  let N₀ := smdl_structure_l I (R := R) mn.2.1
  have limit : N₀.IsLimitOrdinal ⟨μ,step.common.left_rank.1⟩ :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp
      ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
        (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨μ,step.common.left_rank.1⟩)).mp
          step.common.limit)
  intro X T A π L l φ W Z Δ g old low
  have lower := limit.1.transitive κ below ⟨l,old.common.right_rank.1⟩ low
  obtain ⟨l',Z',g',_,_,comp,next⟩ := old.trans_l hZF step hω mn mp mb map ext lower
  let l₀ : N₀.Domain := ⟨l,old.common.right_rank.1⟩
  let Z₀ : N₀.Domain := ⟨Z,old.common.right_rank.2.1⟩
  have rz := (rr_rank_native_l I mn.2.1 hN l₀ Z₀).mp old.common.right_rank
  have sub := (KP.v_compare_l hN rz rank ((v_ordinal_l (kp_pair_l hN) rank).transitive l₀ low)).1
  refine ⟨l',Z',g',next,?_⟩
  intro x y E xy
  let y₀ : N₀.Domain := ⟨y,old.common.injection.1.output_mem_of_pairMember xy⟩
  have hy : N₀.mem y₀ Z₀ := (old.common.image y).mpr
    ⟨x,old.common.injection.1.input_mem_of_pairMember xy,xy⟩
  exact (comp.2 x E).trans ((show
    (∃ z, Rd_entry_d x z g ∧ Rd_entry_d z E t) ↔ Rd_entry_d y E t from
      ⟨fun ⟨z,xz,zE⟩ => old.common.injection.1.1.2 x z y xz xy ▸ zE,
        fun yE => ⟨y,xy,yE⟩⟩).trans (square y₀ (sub y₀ hy) E))

/-- 两条实际活动边同步复合共同层、工作图和原边，更新同一份旧档案。 -/
theorem Ic_agree_d.archive_image_l
    {ω N R B σ P S C τ Y T D υ μ ν ψ U V Γ t L l χ W Z Δ s
      c d e a b RB RC j k κ : M.Domain}
    (first : Ic_agree_d I N R B σ P S C τ μ ν ψ U V Γ t)
    (second : Ic_agree_d I P S C τ Y T D υ L l χ W Z Δ s)
    (hω : M.IsOmega ω) (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (my : Smdl_d I e Y T) (mb : Smem_d I a B RB) (mc : Smem_d I b C RC)
    (map : Smap_d I ω c a N B σ) (copy : Smap_d I ω d b P C τ)
    (hP : (smdl_structure_l I (R := S) mp.2.1).Models KP)
    (ext : Extensional (smdl_structure_l I (R := T) my.2.1))
    (κ₀ K : (smdl_structure_l I (R := S) mp.2.1).Domain)
    (rank : V_d (kp_pair_l hP) κ₀ K) (point : Rd_entry_d κ κ₀.val t)
    (below : Rd_entry_d κ μ R) (above : Rd_entry_d κ₀.val L S)
    (inverse : ∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x t)
    (square : ∀ x : (smdl_structure_l I (R := S) mp.2.1).Domain, ∀ y E,
      (smdl_structure_l I (R := S) mp.2.1).mem x K → Rd_entry_d x.val y k →
        (Rd_entry_d x.val E s ↔ Rd_entry_d y E j)) :
    Ic_archive_image_d I N R B σ Y T D υ j κ := by
  let N₀ := smdl_structure_l I (R := R) mn.2.1
  let P₀ := smdl_structure_l I (R := S) mp.2.1
  have limit : N₀.IsLimitOrdinal ⟨μ,first.common.left_rank.1⟩ :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp
      ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
        (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨μ,first.common.left_rank.1⟩)).mp
          first.common.limit)
  have limit' : P₀.IsLimitOrdinal ⟨L,second.common.left_rank.1⟩ :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp
      ((rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest)
        (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨L,second.common.left_rank.1⟩)).mp
          second.common.limit)
  intro X S₀ A π L₀ l₀ φ A₀ B₀ D₀ g old low
  have low₀ := limit.1.transitive ⟨κ,(mn.2.2.2 κ μ below).1⟩ below
    ⟨l₀,old.common.right_rank.1⟩ low
  obtain ⟨l₁,B₁,g₁,il,_,comp₁,old₁⟩ := old.trans_l hZF first hω mn mp mb map hP.1 low₀
  have low₁ : P₀.mem ⟨l₁,old₁.common.right_rank.1⟩ κ₀ :=
    (first.common.pred κ κ₀.val point l₁).mpr ⟨l₀,low,il⟩
  have low₂ := limit'.1.transitive κ₀ above ⟨l₁,old₁.common.right_rank.1⟩ low₁
  obtain ⟨l₂,B₂,g₂,_,_,comp₂,old₂⟩ := old₁.trans_l hZF second hω mp my mc copy ext low₂
  let a₀ : P₀.Domain := ⟨l₁,old₁.common.right_rank.1⟩
  let B₁₀ : P₀.Domain := ⟨B₁,old₁.common.right_rank.2.1⟩
  have rb := (rr_rank_native_l I mp.2.1 hP a₀ B₁₀).mp old₁.common.right_rank
  have sub := (KP.v_compare_l hP rb rank ((v_ordinal_l (kp_pair_l hP) rank).transitive a₀ low₁)).1
  refine ⟨l₂,B₂,g₂,old₂,?_⟩
  intro x y E xy
  obtain ⟨z,hz,xz⟩ := old₁.common.injection.1.2.2 x (old.common.injection.1.input_mem_of_pairMember xy)
  obtain ⟨y₀,xy₀,yz⟩ := (comp₁.2 x z).mp xz
  have eq := old.common.injection.1.1.2 x y₀ y xy₀ xy
  subst y₀
  have hzB : P₀.mem ⟨z,hz⟩ B₁₀ := (old₁.common.image z).mpr
    ⟨x,old₁.common.injection.1.input_mem_of_pairMember xz,xz⟩
  have value := square ⟨z,hz⟩ y E (sub ⟨z,hz⟩ hzB) ((inverse z y).mpr yz)
  exact (comp₂.2 x E).trans ((show
    (∃ z', Rd_entry_d x z' g₁ ∧ Rd_entry_d z' E s) ↔ Rd_entry_d z E s from
      ⟨fun ⟨z',xz',zE⟩ => old₁.common.injection.1.1.2 x z' z xz' xz ▸ zE,
        fun zE => ⟨z,xz,zE⟩⟩).trans value)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 档案共同层与工作共同层的识别

源支撑相同时，秩对象先沿已有复制图识别。两个完整前驱图的定义域于是相同，
内部良基性与目标外延性识别整张图，并进一步识别目标端点和秩对象。
因此原档案的实际共同层可以直接使用工作侧的交换方块。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_agree_d.common_unique_l
    {ω X R A π N S B σ L l φ U V D t l' U' V' D' t' c a T : M.Domain}
    (h : Ic_agree_d I X R A π N S B σ L l φ U V D t)
    (g : Ic_common_d I X R N S L l' U' V' D' t')
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (ma : Smem_d I a A T)
    (map : Smap_d I ω c a X A π) (ext : Rf_ext_d I N S) :
    l = l' ∧ U = U' ∧ V = V' ∧ D = D' ∧ t = t' := by
  obtain ⟨W,hw,_,rank,_,uw,_⟩ := h.work
  obtain ⟨W',hw',uw'⟩ := map.1.1.2.2 U' g.left_rank.2.1
  have rank' := (rr_rank_mem_l I (ZF.modelsKP hZF) ma h.left_trans
    (map.1.1.output_mem_of_pairMember h.left_end) hw').mp
      ((rr_rank_truth_l I).mpr (((rr_rank_truth_l I).mp g.left_rank).map_l I hZF hω mx ma.1 map
        (by simp -implicitDefEqProofs) (Fin.cases uw' (fun _ => h.left_end))))
  have eqW := rank'.unique_l hZF h.left_trans hw' hw rank
  have eqU := map.1.2 U' U W (eqW ▸ uw') uw
  subst U'
  have eqD := hZF.1.eq_of_same_members D' D (fun x => (g.carrier x).trans (h.common.carrier x).symm)
  subst D'
  have trans := rank.transitive_l h.left_trans hw
  have down x y (hx : M.mem x D) (yx : Rd_entry_d y x R) : M.mem y D := by
    obtain ⟨x',hx',xx⟩ := map.1.1.2.2 x ((h.common.carrier x).mp hx).1
    obtain ⟨y',hy',yy⟩ := map.1.1.2.2 y (mx.2.2.2 y x yx).1
    have xw := ((ma.2 x' W).mp ((map.relation_l I hZF hω mx ma.1 xx uw).mp
      ((h.common.carrier x).mp hx).2)).2.2
    have yx' := ((ma.2 y' x').mp ((map.relation_l I hZF hω mx ma.1 yy xx).mp yx)).2.2
    exact (h.common.carrier y).mpr ⟨map.1.1.input_mem_of_pairMember yy,
      (map.relation_l I hZF hω mx ma.1 yy uw).mpr
        ((ma.2 y' W).mpr ⟨hy',hw,trans x' xw y' yx'⟩)⟩
  -- 良基性来自指定工作嵌入；不要求原模型外部良基。
  obtain ⟨R₀,wf,relation⟩ := wf_membership_l hZF A
  have wfX : Wf_rel_d X R := wf_of_map_l hZF wf
    (fn0_of_function_l (ZF.modelsKP hZF) map.1.1) (fun x y x' y' xy xx yy =>
      (relation x' y').mpr ((ma.2 x' y').mp ((map.relation_l I hZF hω mx ma.1 xx yy).mp xy)))
  have same := rf_full_overlap_l hZF wfX (fun x hx => ((h.common.carrier x).mp hx).1)
    h.common.injection.1 g.injection.1 down down h.common.pred g.pred ext
  have graph x y : Rd_entry_d x y t ↔ Rd_entry_d x y t' := by
    constructor
    · intro xy
      obtain ⟨z,_,xz⟩ := g.injection.1.2.2 x (h.common.injection.1.input_mem_of_pairMember xy)
      exact (same x y z xy xz).symm ▸ xz
    · intro xy
      obtain ⟨z,_,xz⟩ := h.common.injection.1.2.2 x (g.injection.1.input_mem_of_pairMember xy)
      exact same x z y xz xy ▸ xz
  have eqt := h.common.injection.1.1.1.eq_of_pairMember_iff hZF.1 g.injection.1.1.1 graph
  subst t'
  have eql := ext l h.common.endpoint.2.1 l' g.endpoint.2.1
    (fun x _ => (h.common.endpoint.2.2 x).trans (g.endpoint.2.2 x).symm)
  have eqV := ext V h.common.right_rank.2.1 V' g.right_rank.2.1
    (fun x _ => (h.common.image x).trans (g.image x).symm)
  exact ⟨eql,rfl,eqV,rfl,rfl⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同秩段中的严格极限切片

源支撑的不可数共尾性给出 τ<τ+ω<L。实际 V_(τ+ω) 和它的完整历史沿
同一共同图搬运，目标切片因而包含指定临界点并严格属于目标共同秩段。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hK : M.Models KP)
local notation "I" => kp_pair_l hK

theorem Ic_common_d.limit_cut_l {X R Y S L l U V Γ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (nx : ∃ x, M.mem x X) (ny : ∃ x, M.mem x Y)
    (hX : (smdl_structure_l I (R := R) nx).Models ZF)
    (hY : (smdl_structure_l I (R := S) ny).Models KP)
    (w χ τ : (smdl_structure_l I (R := R) nx).Domain)
    (κ : (smdl_structure_l I (R := S) ny).Domain)
    (omega : (smdl_structure_l I (R := R) nx).IsOmega w)
    (cofinal : (smdl_structure_l I (R := R) nx).IsCofinality (kp_pair_l (ZF.modelsKP hX))
      χ ⟨L, common.left_rank.1⟩)
    (uncountable : (smdl_structure_l I (R := R) nx).mem w χ)
    (below : (smdl_structure_l I (R := R) nx).mem τ ⟨L, common.left_rank.1⟩)
    (point : Rd_entry_d τ.val κ.val t) :
    ∃ α β : (smdl_structure_l I (R := S) ny).Domain,
      (smdl_structure_l I (R := S) ny).mem α ⟨l, common.right_rank.1⟩ ∧
      (smdl_structure_l I (R := S) ny).mem β ⟨V, common.right_rank.2.1⟩ ∧
      (smdl_structure_l I (R := S) ny).mem κ β ∧
      (smdl_structure_l I (R := S) ny).IsLimitOrdinal α ∧ V_d (kp_pair_l hY) α β ∧
      ∀ δ : (smdl_structure_l I (R := S) ny).Domain,
        (smdl_structure_l I (R := S) ny).IsLimitOrdinal δ →
        (smdl_structure_l I (R := S) ny).mem κ δ →
        (smdl_structure_l I (R := S) ny).MemberSubset α δ := by
  let X₀ := smdl_structure_l I (R := R) nx
  let Y₀ := smdl_structure_l I (R := S) ny
  let J := kp_pair_l (ZF.modelsKP hX)
  let L₀ : X₀.Domain := ⟨L, common.left_rank.1⟩
  let U₀ : X₀.Domain := ⟨U, common.left_rank.2.1⟩
  have rankU := (rr_rank_native_l I nx (ZF.modelsKP hX) L₀ U₀).mp common.left_rank
  have trans := v_transitive_l J rankU
  have limit : X₀.IsLimitOrdinal L₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I nx (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => L₀)).mp common.limit)
  obtain ⟨a, _, ha, hτa, haL, least⟩ := ZF.oa_omega_bound_l hX J omega limit cofinal uncountable below
  obtain ⟨B, rankB⟩ := ZF.v_exists_l J hX ha.1
  have haU := ZF.v_ordinal_mem_l J hX rankU haL
  have hBU := ZF.v_mem_l J hX rankB rankU haL
  have hτB := ZF.v_ordinal_mem_l J hX rankB hτa
  have pick (x : X₀.Domain) (hx : X₀.mem x U₀) :
      ∃ y : Y₀.Domain, Rd_entry_d x.val y.val t := by
    obtain ⟨y, hy, xy⟩ := common.injection.1.2.2 x.val ((common.carrier x.val).mpr ⟨x.property, hx⟩)
    exact ⟨⟨y, hy⟩, xy⟩
  obtain ⟨α, ia⟩ := pick a haU
  obtain ⟨β, ib⟩ := pick B hBU
  let nu : Nonempty {x : X₀.Domain // X₀.mem x U₀} := ⟨⟨a, haU⟩⟩
  -- 先把源的实际秩历史收回共同层，再搬运全部层值方程。
  obtain ⟨F, hF, history⟩ := KP.v_history_inside_l (ZF.modelsKP hX) rankU limit haU hBU rankB
  have relative : Vr_d U₀ a B := ⟨B, F, hBU, hF, fun x _ => history x⟩
  have rank := rr_native_rank_value_l I nx ny hY.1 U₀ a B trans common.carrier common.injection
    common.image common.pred common.right_closed haU hBU ia ib
    ((vr_sat_l (ZF.modelsKP hX) trans nu _ (.bound 1) .newest).mpr relative)
  let ρ : Env (rt_model_l U₀ nu) 1 := ⟨fun _ => ⟨a, haU⟩, fun _ => ⟨a, haU⟩⟩
  let η : Env Y₀ 1 := ⟨fun _ => α, fun _ => α⟩
  have limit' : Y₀.IsLimitOrdinal α := (KP.limit0_sat_l hY η .newest).mp
    ((rr_native_delta_l I nx ny U₀ trans nu common.carrier common.injection common.pred
      (KP.limit0_m .newest) (by simp -implicitDefEqProofs) (KP.limit0_delta_l _)
      ρ η (fun _ => ia)).mp ((KP.limit0_sat_l (ZF.modelsKP hX) _ .newest).mpr ha))
  -- “两端之间没有极限序数”是有界公式；完整前驱图保持 τ+ω 的最小性。
  let ψ : Formula 1 2 := .forallMem (.bound 1)
    (.imp (KP.limit0_m .newest) (.neg (.mem (.bound 1) .newest)))
  have closed : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed]
  have delta : ψ.IsDelta0 := .forallMem _ (.imp (KP.limit0_delta_l _) (.neg (.mem ..)))
  have hτU := ZF.v_ordinal_mem_l J hX rankU below
  let ρ₀ : Env (rt_model_l U₀ nu) 2 :=
    ⟨Fin.cases ⟨τ,hτU⟩ (fun _ => ⟨a,haU⟩),fun _ => ⟨τ,hτU⟩⟩
  let η₀ : Env Y₀ 2 := ⟨Fin.cases κ (fun _ => α),fun _ => κ⟩
  have minimal : Formula.satisfies (image_env_l Subtype.val ρ₀) ψ := by
    simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, KP.limit0_sat_l (ZF.modelsKP hX),
      Definitional.Term.eval_newest]
    intro δ hδ limitδ hτδ
    exact KP.mem_irrefl_d (ZF.modelsKP hX) δ (least δ limitδ hτδ δ hδ)
  have minimal := (rr_native_delta_l I nx ny U₀ trans nu common.carrier common.injection common.pred
    ψ closed delta ρ₀ η₀ (Fin.cases point (fun _ => ia))).mp minimal
  simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_neg_iff, Formula.satisfies_mem_iff, KP.limit0_sat_l hY,
    Definitional.Term.eval_newest] at minimal
  exact ⟨α, β, (common.endpoint.2.2 α.val).mpr ⟨a.val, a.property, haL, ia⟩,
    (common.image β.val).mpr ⟨B.val, common.injection.1.input_mem_of_pairMember ib, ib⟩,
    (common.pred B.val β.val ib κ.val).mpr ⟨τ.val, hτB, point⟩, limit',
    (rr_rank_native_l I ny hY α β).mp rank, fun δ limitδ hκδ x hx => by
      rcases limit'.1.trichotomy hY.1 limitδ.1 (KP.difference_exists_d hY)
          (KP.intersection_exists_d hY α δ) with eq | lt | gt
      · exact (eq x).mp hx
      · exact limitδ.1.transitive α lt x hx
      · exact (minimal δ gt limitδ hκδ).elim⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真实共同层的高度唯一性

共同图在重叠部分由两侧复制图唯一确定。若两个最大覆盖高度不同，
较高共同层就会实现较低共同层的全局缺失子集，矛盾。因此历史端点
属于实际两行的比较，不依赖任意选取的支撑码或共同层见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 支撑的每个原成员都在同一共同图的定义域内。 -/
theorem Ic_agree_d.domain_l
    {ω X R A π N S B σ L l φ U V D t c a T x : M.Domain}
    (h : Ic_agree_d I X R A π N S B σ L l φ U V D t)
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (ma : Smem_d I a A T)
    (map : Smap_d I ω c a X A π) (hx : Rd_entry_d x L R) : M.mem x D := by
  have hxX := (mx.2.2.2 x L hx).1
  obtain ⟨y, hy, hxy⟩ := map.1.1.2.2 x hxX
  have hyφ := ((ma.2 y φ).mp ((map.relation_l I hZF hω mx ma.1 hxy h.left_end).mp hx)).2.2
  obtain ⟨W, hwA, _, rank, _, hUW, _⟩ := h.work
  have hyW := rank.ordinal_subset_l hZF h.left_trans hwA y hyφ
  exact (h.common.carrier x).mpr ⟨hxX, (map.relation_l I hZF hω mx ma.1 hxy hUW).mpr
    ((ma.2 y W).mpr ⟨hy, hwA, hyW⟩)⟩

/-- 同两行的最大共同层具有同一个原支撑、原生端点及工作高度。 -/
theorem Ic_agree_d.height_unique_l
    {ω X R A π N S B σ L l φ U V D t L' l' φ' U' V' D' t' c a T : M.Domain}
    (h : Ic_agree_d I X R A π N S B σ L l φ U V D t)
    (g : Ic_agree_d I X R A π N S B σ L' l' φ' U' V' D' t')
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (ma : Smem_d I a A T)
    (map : Smap_d I ω c a X A π) (inj : M.IsSetInjectionFromTo I σ N B) :
    L = L' ∧ l = l' ∧ φ = φ' := by
  have no {L l φ U V D t L' l' φ' U' V' D' t'}
      (h : Ic_agree_d I X R A π N S B σ L l φ U V D t)
      (g : Ic_agree_d I X R A π N S B σ L' l' φ' U' V' D' t') (lt : M.mem φ φ') : False := by
    have hLL := (map.relation_l I hZF hω mx ma.1 h.left_end g.left_end).mpr
      ((ma.2 φ φ').mpr ⟨map.1.1.output_mem_of_pairMember h.left_end,
        map.1.1.output_mem_of_pairMember g.left_end, lt⟩)
    obtain ⟨x, hx, sub, missing⟩ := h.common.exactness.2.2
    obtain ⟨E, rep⟩ := g.common.exactness.2.1 L h.common.left_rank.1 hLL x hx sub
    have same y (hy : M.mem y X) (hyx : Rd_entry_d y x R) P :
        Rd_entry_d y P t' ↔ Rd_entry_d y P t := by
      have hyL := sub y hy hyx
      obtain ⟨y', hy', yy⟩ := map.1.1.2.2 y hy
      have hyφ := ((ma.2 y' φ).mp ((map.relation_l I hZF hω mx ma.1 yy h.left_end).mp hyL)).2.2
      have hyL' := (map.relation_l I hZF hω mx ma.1 yy g.left_end).mpr
        ((ma.2 y' φ').mpr ⟨hy', map.1.1.output_mem_of_pairMember g.left_end,
          g.limit.1.transitive φ lt y' hyφ⟩)
      obtain ⟨P₀, _, yt⟩ := h.common.injection.1.2.2 y (h.domain_l hZF hω mx ma map hyL)
      obtain ⟨P₁, _, ys⟩ := g.common.injection.1.2.2 y (g.domain_l hZF hω mx ma map hyL')
      constructor
      · intro yp
        exact (inj.2 P₀ P y' (h.points y y' P₀ yy yt) (g.points y y' P yy yp)) ▸ yt
      · intro yp
        exact (inj.2 P₁ P y' (g.points y y' P₁ yy ys) (h.points y y' P yy yp)) ▸ ys
    apply missing E
    refine ⟨hx, rep.2.1, fun P => (rep.2.2 P).trans ?_⟩
    exact exists_congr fun y => and_congr_right fun hy => and_congr_right fun hyx => same y hy hyx P
  have eq : φ = φ' := by
    rcases h.limit.1.trichotomy hZF.1 g.limit.1 (KP.difference_exists_d (ZF.modelsKP hZF))
        (KP.intersection_exists_d (ZF.modelsKP hZF) φ φ') with eq | lt | gt
    · exact hZF.1.eq_of_same_members φ φ' eq
    · exact (no h g lt).elim
    · exact (no g h gt).elim
  exact ⟨map.1.2 L L' φ' (eq ▸ h.left_end) g.left_end,
    inj.2 l l' φ' (eq ▸ h.right_end) g.right_end, eq⟩

/-- 相同原模型及相同复制图之间不存在带全局缺失见证的共同层。 -/
theorem Ic_agree_d.not_refl_l
    {ω X R A π L l φ U V D t c a T : M.Domain}
    (h : Ic_agree_d I X R A π X R A π L l φ U V D t)
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (ma : Smem_d I a A T)
    (map : Smap_d I ω c a X A π) : False := by
  have fixed y E (hyE : Rd_entry_d y E t) : y = E := by
    obtain ⟨y', _, yy⟩ := map.1.1.2.2 y
      ((h.common.carrier y).mp (h.common.injection.1.input_mem_of_pairMember hyE)).1
    exact map.1.2 y E y' yy (h.points y y' E yy hyE)
  obtain ⟨x, hx, sub, missing⟩ := h.common.exactness.2.2
  apply missing x
  refine ⟨hx, hx, fun P => ⟨?_, ?_⟩⟩
  · intro hp
    have hP := (mx.2.2.2 P x hp).1
    obtain ⟨E, _, pe⟩ := h.common.injection.1.2.2 P (h.domain_l hZF hω mx ma map (sub P hP hp))
    exact ⟨P, hP, hp, (fixed P E pe).symm ▸ pe⟩
  · rintro ⟨y, _, hy, yp⟩
    exact fixed y P yp ▸ hy

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同原秩段内的标签图与相邻元数

自然数标签图的全部配对坐标低于 ω，因此图本身属于包含 ω 的极限秩段。
同一完整前驱图搬运整张函数图和两个后继关系，元数可以是原模型的非标准有限元数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.labels_l {X R N S L l U V Γ t : M.Domain}
    (h : Ic_common_d I X R N S L l U V Γ t)
    (nx : ∃ x, M.mem x X) (nn : ∃ x, M.mem x N)
    (hX : (smdl_structure_l I (R := R) nx).Models KP)
    (en : Extensional (smdl_structure_l I (R := S) nn))
    (w k a n f : (smdl_structure_l I (R := R) nx).Domain)
    (w' n' : (smdl_structure_l I (R := S) nn).Domain)
    (omega : (smdl_structure_l I (R := R) nx).IsOmega w)
    (hn : (smdl_structure_l I (R := R) nx).mem n w)
    (first : (smdl_structure_l I (R := R) nx).SuccessorOf a k)
    (last : (smdl_structure_l I (R := R) nx).SuccessorOf n a)
    (labels : Fn0_d (M := smdl_structure_l I (R := R) nx) k w f)
    (iw : Rd_entry_d w.val w'.val t) (inum : Rd_entry_d n.val n'.val t) :
    ∃ k' a' f' : (smdl_structure_l I (R := S) nn).Domain,
      Rd_entry_d k.val k'.val t ∧ Rd_entry_d a.val a'.val t ∧ Rd_entry_d f.val f'.val t ∧
      Rd_entry_d k'.val V S ∧ Rd_entry_d a'.val V S ∧ Rd_entry_d f'.val V S ∧
      Fn0_d (M := smdl_structure_l I (R := S) nn) k' w' f' ∧
      (smdl_structure_l I (R := S) nn).SuccessorOf a' k' ∧
      (smdl_structure_l I (R := S) nn).SuccessorOf n' a' := by
  let X₀ := smdl_structure_l I (R := R) nx
  let N₀ := smdl_structure_l I (R := S) nn
  let U₀ : X₀.Domain := ⟨U, h.left_rank.2.1⟩
  let L₀ : X₀.Domain := ⟨L, h.left_rank.1⟩
  have rank := (rr_rank_native_l I nx hX L₀ U₀).mp h.left_rank
  have trans := v_transitive_l (kp_pair_l hX) rank
  have limit : X₀.IsLimitOrdinal L₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I nx (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => L₀)).mp h.limit)
  have hwU : X₀.mem w U₀ := ((h.carrier w.val).mp (h.injection.1.input_mem_of_pairMember iw)).2
  have haω := omega.transitive hX n hn a last.predecessor_mem
  have hkω := omega.transitive hX a haω k first.predecessor_mem
  have hfU : X₀.mem f U₀ := v_relation_mem_l (kp_pair_l hX) rank limit hwU (fun p hp => by
    obtain ⟨i, hi, y, hy, pair⟩ := labels.1 p hp
    exact ⟨i, omega.transitive hX k hkω i hi, y, hy, pair⟩)
  have pick (x : X₀.Domain) (hx : X₀.mem x U₀) :
      ∃ y : N₀.Domain, Rd_entry_d x.val y.val t ∧ Rd_entry_d y.val V S := by
    have dom := (h.carrier x.val).mpr ⟨x.property, hx⟩
    obtain ⟨y, hy, pair⟩ := h.injection.1.2.2 x.val dom
    exact ⟨⟨y, hy⟩, pair, (h.image y).mpr ⟨x.val, dom, pair⟩⟩
  obtain ⟨k', ik, hkV⟩ := pick k (trans w hwU k hkω)
  obtain ⟨a', ia, haV⟩ := pick a (trans w hwU a haω)
  obtain ⟨f', ifn, hfV⟩ := pick f hfU
  have fn := (rr_native_function_l I nx nn hX.1 en U₀ trans h.carrier h.injection h.pred
    k w f k' w' f' ik iw ifn labels).1
  let nu : Nonempty {x : X₀.Domain // X₀.mem x U₀} := ⟨⟨w, hwU⟩⟩
  have successor (x y : X₀.Domain) (x' y' : N₀.Domain)
      (ix : Rd_entry_d x.val x'.val t) (iy : Rd_entry_d y.val y'.val t)
      (succ : X₀.SuccessorOf x y) : N₀.SuccessorOf x' y' := by
    have hx := ((h.carrier x.val).mp (h.injection.1.input_mem_of_pairMember ix)).2
    have hy := ((h.carrier y.val).mp (h.injection.1.input_mem_of_pairMember iy)).2
    let ρ : Env (rt_model_l (M := X₀) U₀ nu) 2 :=
      ⟨Fin.cases ⟨x, hx⟩ (fun _ => ⟨y, hy⟩), fun _ => ⟨x, hx⟩⟩
    let θ : Env N₀ 2 := ⟨Fin.cases x' (fun _ => y'), fun _ => x'⟩
    exact (KP.succ0_sat_l en θ .newest (.bound 1)).mp
      ((rr_native_delta_l I nx nn U₀ trans nu h.carrier h.injection h.pred
        (KP.succ0_m .newest (.bound 1)) (by simp -implicitDefEqProofs) (KP.succ0_delta_l ..)
        ρ θ (Fin.cases ix (fun _ => iy))).mp ((KP.succ0_sat_l hX.1 _ .newest (.bound 1)).mpr succ))
  exact ⟨k', a', f', ik, ia, ifn, hkV, haV, hfV, fn,
    successor a k a' k' ia ik first, successor n a n' a' inum ia last⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 含恒等步的原生复制历史

活动区间保存原生共同层、全局缺失及工作侧对应。原关系码绑定原树的
同一模型列；恒等区间也保存相同模型码，避免把同载体的不同关系混同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ic_past_d (I : kpair_convention_l.Interpretation M) (Q L i j X A π Y B σ : M.Domain) : Prop :=
  (∃ c, Rd_entry_d i c Q ∧ Rd_entry_d j c Q ∧ X = Y ∧ A = B ∧ π = σ ∧ ∀ ρ, ¬ Rd_entry_d i ρ L) ∨
  ∃ k ρ l φ U V D t c d R S, (i = k ∨ M.mem i k) ∧ M.mem k j ∧ Rd_entry_d k ρ L ∧
    (∀ ν, Rd_entry_d i ν L → i = k) ∧ Rd_entry_d i c Q ∧ Rd_entry_d j d Q ∧
    Smdl_d I c X R ∧ Smdl_d I d Y S ∧ Ic_agree_d I X R A π Y S B σ ρ l φ U V D t

def ic_past_m {d} (Q L i j X A π Y B σ : Term d) : Formula 1 d := set[d] ⟪
  (∃ c, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, c, ⌜Q⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜j⌝ₛ, c, ⌜Q⌝ₛ) ∧
    ⌜X⌝ₛ = ⌜Y⌝ₛ ∧ ⌜A⌝ₛ = ⌜B⌝ₛ ∧ ⌜π⌝ₛ = ⌜σ⌝ₛ ∧
    (∀ ρ, ¬ ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ρ, ⌜L⌝ₛ))) ∨
  (∃ k ρ l φ U V D t c d R S,
    (⌜i⌝ₛ = k ∨ ⌜i⌝ₛ ∈ k) ∧ k ∈ ⌜j⌝ₛ ∧ ⌜rd_entry0_m⌝ₚ(k, ρ, ⌜L⌝ₛ) ∧
    (∀ ν, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, ν, ⌜L⌝ₛ) → ⌜i⌝ₛ = k) ∧
    ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, c, ⌜Q⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜j⌝ₛ, d, ⌜Q⌝ₛ) ∧
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c, ⌜X⌝ₛ, R) ∧ ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(d, ⌜Y⌝ₛ, S) ∧
    ⌜ic_agree_m⌝ₚ(⌜X⌝ₛ, R, ⌜A⌝ₛ, ⌜π⌝ₛ, ⌜Y⌝ₛ, S, ⌜B⌝ₛ, ⌜σ⌝ₛ, ρ, l, φ, U, V, D, t))⟫
derive_free_closed ic_past_m

theorem ic_past_sat_l (hKP : M.Models KP) {d} (η : Env M d) (Q L i j X A π Y B σ : Term d) :
    Formula.satisfies η (ic_past_m Q L i j X A π Y B σ) ↔
      Ic_past_d (kp_pair_l hKP) (Q.eval η) (L.eval η) (i.eval η) (j.eval η) (X.eval η) (A.eval η)
        (π.eval η) (Y.eval η) (B.eval η) (σ.eval η) := by
  simp only [ic_past_m, Ic_past_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_forall_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hKP.1, smdl_sat_l (kp_pair_l hKP), ic_agree_sat_l hKP, Definitional.Term.eval_weaken]; rfl

variable {I : kpair_convention_l.Interpretation M}

theorem Ic_past_d.prior_l {Q L i j X A π Y B σ : M.Domain} (h : Ic_past_d I Q L i j X A π Y B σ) :
    (∃ c, Rd_entry_d i c Q ∧ Rd_entry_d j c Q ∧ X = Y ∧ A = B ∧ π = σ) ∨
      ∃ ρ l φ U V D t c d R S, Rd_entry_d i c Q ∧ Rd_entry_d j d Q ∧
        Smdl_d I c X R ∧ Smdl_d I d Y S ∧ Ic_agree_d I X R A π Y S B σ ρ l φ U V D t := by
  rcases h with ⟨c, hi, hj, ex, ea, ep, _⟩ | ⟨_, ρ, l, φ, U, V, D, t, c, d, R, S, _, _, _, _, rest⟩
  · exact Or.inl ⟨c, hi, hj, ex, ea, ep⟩
  · exact Or.inr ⟨ρ, l, φ, U, V, D, t, c, d, R, S, rest⟩

theorem Ic_past_d.active_l {Q L i j X A π Y B σ ρ : M.Domain}
    (h : Ic_past_d I Q L i j X A π Y B σ)
    (hf : ∀ s t, Rd_entry_d i s L → Rd_entry_d i t L → s = t)
    (hi : Rd_entry_d i ρ L) :
    ∃ l φ U V D t c d R S, Rd_entry_d i c Q ∧ Rd_entry_d j d Q ∧
      Smdl_d I c X R ∧ Smdl_d I d Y S ∧ Ic_agree_d I X R A π Y S B σ ρ l φ U V D t := by
  rcases h with ⟨_, _, _, _, _, _, no⟩ | ⟨k, μ, l, φ, U, V, D, t, c, d, R, S, _, _, hm, first, rest⟩
  · exact (no ρ hi).elim
  · have eq := first ρ hi
    subst k
    have eq := hf μ ρ hm hi
    subst μ
    exact ⟨l, φ, U, V, D, t, c, d, R, S, rest⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生共同层的完整延伸

只比较给定原模型中的两份实际秩历史。KP 的有界秩比较与历史回收
供应复合所需的全部局部证书；端点严格下降到新端点以下，由同一完整前驱图读取。
本层不使用工作模型、复制图或任意共同图的唯一性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同域共同图的逐点原边方程给出完整图复合。 -/
theorem Ic_common_d.graph_comp_l
    {X R N S Y T L l l' U V V' Γ g g' j : M.Domain}
    (old : Ic_common_d I X R N S L l U V Γ g)
    (next : Ic_common_d I X R Y T L l' U V' Γ g')
    (graph : ∀ x y E, Rd_entry_d x y g → (Rd_entry_d x E g' ↔ Rd_entry_d y E j)) :
    It_comp_d g j g' := by
  refine ⟨next.injection.1.1.1,fun x E => ⟨?_,?_⟩⟩
  · intro hx
    obtain ⟨y,_,xy⟩ := old.injection.1.2.2 x (next.injection.1.input_mem_of_pairMember hx)
    exact ⟨y,xy,(graph x y E xy).mp hx⟩
  · rintro ⟨y,xy,yE⟩
    exact (graph x y E xy).mpr yE

/-- 原生 KP 从严格高度比较生产局部秩历史，再复合同一两张共同图。 -/
theorem Ic_common_d.native_trans_l
    {X R N S P T L l U V Γ g μ ν A B Δ t c d : M.Domain}
    (old : Ic_common_d I X R N S L l U V Γ g)
    (step : Ic_common_d I N S P T μ ν A B Δ t)
    (mn : Smdl_d I c N S) (mp : Smdl_d I d P T)
    (hN : (smdl_structure_l I (R := S) mn.2.1).Models KP)
    (ext : Extensional (smdl_structure_l I (R := T) mp.2.1))
    (below : Rd_entry_d l μ S) :
    ∃ l' V' g', Rd_entry_d l l' t ∧ Rd_entry_d V V' t ∧ It_comp_d g t g' ∧
      Ic_common_d I X R P T L l' U V' Γ g' ∧ Rd_entry_d l' ν T := by
  let N₀ := smdl_structure_l I (R := S) mn.2.1
  let μ₀ : N₀.Domain := ⟨μ,step.left_rank.1⟩
  let A₀ : N₀.Domain := ⟨A,step.left_rank.2.1⟩
  let l₀ : N₀.Domain := ⟨l,old.right_rank.1⟩
  let V₀ : N₀.Domain := ⟨V,old.right_rank.2.1⟩
  have upper : V_d (kp_pair_l hN) μ₀ A₀ := (rr_rank_native_l I mn.2.1 hN μ₀ A₀).mp step.left_rank
  have lower : V_d (kp_pair_l hN) l₀ V₀ := (rr_rank_native_l I mn.2.1 hN l₀ V₀).mp old.right_rank
  have limit : N₀.IsLimitOrdinal μ₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => μ₀)).mp step.limit)
  have hlA : N₀.mem l₀ A₀ := KP.v_ordinal_subset_l hN upper l₀ below
  have hVA : N₀.mem V₀ A₀ := (KP.v_compare_l hN lower upper (limit.1.transitive l₀ below)).2 below
  obtain ⟨F,hF,cert⟩ := KP.v_history_inside_l hN upper limit hlA hVA lower
  have localrank : Vr_d A₀ l₀ V₀ := ⟨V₀,F,hVA,hF,fun x _ => cert x⟩
  have trans : Rr_truth_d I N S (Formula.isTransitive .newest) (fun _ : Fin 1 => A) :=
    (rr_truth_native_l I mn.2.1 (Formula.isTransitive .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => A₀)).mpr
        ((Formula.satisfies_isTransitive_iff ..).mpr (v_transitive_l (kp_pair_l hN) upper))
  let p : Fin 3 → N₀.Domain := Fin.cases V₀ (Fin.cases l₀ (fun _ => A₀))
  let ρ : Env N₀ 3 := ⟨p,fun _ => p 0⟩
  have nativeRank : Formula.satisfies ρ (pn_rank_m (.bound 2) (.bound 1) .newest) := by
    apply (pn_rank_sat_l (M := N₀) hN ρ (.bound 2) (.bound 1) .newest).mpr
    exact localrank
  have values : (fun i => (p i).val) = Fin.cases V (Fin.cases l (fun _ : Fin 1 => A)) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  have rank : Rr_truth_d I N S (pn_rank_m (.bound 2) (.bound 1) .newest)
      (Fin.cases V (Fin.cases l (fun _ : Fin 1 => A))) := by
    rw [← values]
    exact (rr_truth_native_l I mn.2.1 _ (by simp -implicitDefEqProofs) p).mpr nativeRank
  obtain ⟨l',V',g',il,iV,comp,common⟩ := old.trans_l hZF step mn mp ext trans hlA hVA rank
  exact ⟨l',V',g',il,iV,comp,common,(step.endpoint.2.2 l').mpr ⟨l,old.right_rank.1,below,il⟩⟩

/-- 原工厂的低秩方块将一次共同图复合识别为同一原树边。 -/
theorem Ic_common_d.native_archive_step_l
    {N R P S μ ν U V Γ t c d j : M.Domain}
    (step : Ic_common_d I N R P S μ ν U V Γ t)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (ext : Extensional (smdl_structure_l I (R := S) mp.2.1))
    (κ K : (smdl_structure_l I (R := R) mn.2.1).Domain)
    (rank : V_d (kp_pair_l hN) κ K) (below : Rd_entry_d κ.val μ R)
    (square : ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      (smdl_structure_l I (R := R) mn.2.1).mem x K → ∀ E, Rd_entry_d x.val E t ↔ Rd_entry_d x.val E j) :
    ∀ X S₀ L l A B Δ g, Ic_common_d I X S₀ N R L l A B Δ g → Rd_entry_d l κ.val R →
      ∃ l' B' g', Ic_common_d I X S₀ P S L l' A B' Δ g' ∧ Rd_entry_d l' ν S ∧
        ∀ x y E, Rd_entry_d x y g → (Rd_entry_d x E g' ↔ Rd_entry_d y E j) := by
  let N₀ := smdl_structure_l I (R := R) mn.2.1
  have limit : N₀.IsLimitOrdinal ⟨μ,step.left_rank.1⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨μ,step.left_rank.1⟩)).mp step.limit)
  intro X S₀ L l A B Δ g old low
  have lower := limit.1.transitive κ below ⟨l,old.right_rank.1⟩ low
  obtain ⟨l',B',g',_,_,comp,common,bound⟩ := old.native_trans_l hZF step mn mp hN ext lower
  let l₀ : N₀.Domain := ⟨l,old.right_rank.1⟩
  let B₀ : N₀.Domain := ⟨B,old.right_rank.2.1⟩
  have rb := (rr_rank_native_l I mn.2.1 hN l₀ B₀).mp old.right_rank
  have sub := (KP.v_compare_l hN rb rank ((v_ordinal_l (kp_pair_l hN) rank).transitive l₀ low)).1
  refine ⟨l',B',g',common,bound,?_⟩
  intro x y E xy
  let y₀ : N₀.Domain := ⟨y,old.injection.1.output_mem_of_pairMember xy⟩
  have hy : N₀.mem y₀ B₀ := (old.image y).mpr ⟨x,old.injection.1.input_mem_of_pairMember xy,xy⟩
  exact (comp.2 x E).trans ((show (∃ z, Rd_entry_d x z g ∧ Rd_entry_d z E t) ↔ Rd_entry_d y E t from
    ⟨fun ⟨z,xz,zE⟩ => old.injection.1.1.2 x z y xz xy ▸ zE,fun yE => ⟨y,xy,yE⟩⟩).trans
      (square y₀ (sub y₀ hy) E))

/-- 两次实际共同层复合，保留原偶数边的同一旧档案像和最终严格端点界。 -/
theorem Ic_common_d.native_archive_image_l
    {N R P S Y T μ ν U V Γ t L l W Z Δ s c d e j k κ : M.Domain}
    (first : Ic_common_d I N R P S μ ν U V Γ t)
    (second : Ic_common_d I P S Y T L l W Z Δ s)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S) (my : Smdl_d I e Y T)
    (hN : (smdl_structure_l I (R := R) mn.2.1).Models KP)
    (hP : (smdl_structure_l I (R := S) mp.2.1).Models KP)
    (ext : Extensional (smdl_structure_l I (R := T) my.2.1))
    (κ₀ K : (smdl_structure_l I (R := S) mp.2.1).Domain)
    (rank : V_d (kp_pair_l hP) κ₀ K) (point : Rd_entry_d κ κ₀.val t)
    (below : Rd_entry_d κ μ R) (above : Rd_entry_d κ₀.val L S)
    (inverse : ∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x t)
    (square : ∀ x : (smdl_structure_l I (R := S) mp.2.1).Domain, ∀ y E,
      (smdl_structure_l I (R := S) mp.2.1).mem x K → Rd_entry_d x.val y k →
        (Rd_entry_d x.val E s ↔ Rd_entry_d y E j)) :
    ∀ X S₀ L₀ l₀ A B D g, Ic_common_d I X S₀ N R L₀ l₀ A B D g → Rd_entry_d l₀ κ R →
      ∃ l' B' g', Ic_common_d I X S₀ Y T L₀ l' A B' D g' ∧ Rd_entry_d l' l T ∧
        ∀ x y E, Rd_entry_d x y g → (Rd_entry_d x E g' ↔ Rd_entry_d y E j) := by
  let N₀ := smdl_structure_l I (R := R) mn.2.1
  let P₀ := smdl_structure_l I (R := S) mp.2.1
  have limit : N₀.IsLimitOrdinal ⟨μ,first.left_rank.1⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨μ,first.left_rank.1⟩)).mp first.limit)
  have limit' : P₀.IsLimitOrdinal ⟨L,second.left_rank.1⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mp.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => ⟨L,second.left_rank.1⟩)).mp second.limit)
  intro X S₀ L₀ l₀ A B D g old low
  have low₀ := limit.1.transitive ⟨κ,(mn.2.2.2 κ μ below).1⟩ below ⟨l₀,old.right_rank.1⟩ low
  obtain ⟨l₁,B₁,g₁,il,_,comp₁,old₁,_⟩ := old.native_trans_l hZF first mn mp hN hP.1 low₀
  have low₁ : P₀.mem ⟨l₁,old₁.right_rank.1⟩ κ₀ := (first.pred κ κ₀.val point l₁).mpr ⟨l₀,low,il⟩
  have low₂ := limit'.1.transitive κ₀ above ⟨l₁,old₁.right_rank.1⟩ low₁
  obtain ⟨l₂,B₂,g₂,_,_,comp₂,old₂,bound⟩ := old₁.native_trans_l hZF second mp my hP ext low₂
  let a₀ : P₀.Domain := ⟨l₁,old₁.right_rank.1⟩
  let B₁₀ : P₀.Domain := ⟨B₁,old₁.right_rank.2.1⟩
  have rb := (rr_rank_native_l I mp.2.1 hP a₀ B₁₀).mp old₁.right_rank
  have sub := (KP.v_compare_l hP rb rank ((v_ordinal_l (kp_pair_l hP) rank).transitive a₀ low₁)).1
  refine ⟨l₂,B₂,g₂,old₂,bound,?_⟩
  intro x y E xy
  obtain ⟨z,hz,xz⟩ := old₁.injection.1.2.2 x (old.injection.1.input_mem_of_pairMember xy)
  obtain ⟨y₀,xy₀,yz⟩ := (comp₁.2 x z).mp xz
  have eq := old.injection.1.1.2 x y₀ y xy₀ xy
  subst y₀
  have hzB : P₀.mem ⟨z,hz⟩ B₁₀ := (old₁.image z).mpr ⟨x,old₁.injection.1.input_mem_of_pairMember xz,xz⟩
  have value := square ⟨z,hz⟩ y E (sub ⟨z,hz⟩ hzB) ((inverse z y).mpr yz)
  exact (comp₂.2 x E).trans ((show (∃ z', Rd_entry_d x z' g₁ ∧ Rd_entry_d z' E s) ↔ Rd_entry_d z E s from
    ⟨fun ⟨z',xz',zE⟩ => old₁.injection.1.1.2 x z' z xz' xz ▸ zE,fun zE => ⟨z,xz,zE⟩⟩).trans value)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原共同层的反向施加图

共同层本身的原生秩历史给出向下封闭性。完整值域与前驱方程随后构造
同一共同图的逆图；不经过任何外部工作模型或复制嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.reverse_native_l {X R N S L l U V Γ t c : M.Domain}
    (h : Ic_common_d I X R N S L l U V Γ t) (mx : Smdl_d I c X R)
    (hx : (smdl_structure_l I (R := R) mx.2.1).Models KP) :
    ∃ E k, (∀ x, M.mem x E ↔ M.mem x N ∧ Rd_entry_d x V S) ∧
      M.IsSetInjectionFromTo I k E X ∧
      (∀ y, Rd_entry_d y U R ↔ ∃ x, M.mem x E ∧ Rd_entry_d x y k) ∧
      (∀ x y, Rd_entry_d x y k → ∀ z, Rd_entry_d z y R ↔ ∃ v, Rd_entry_d v x S ∧ Rd_entry_d v z k) ∧
      (∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x t) := by
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Ln : Xn.Domain := ⟨L,h.left_rank.1⟩
  let Un : Xn.Domain := ⟨U,h.left_rank.2.1⟩
  have rank : V_d (kp_pair_l hx) Ln Un := (rr_rank_native_l I mx.2.1 hx Ln Un).mp h.left_rank
  have trans : Xn.TransitiveSet Un := v_transitive_l (kp_pair_l hx) rank
  have down (x y : M.Domain) (hΓ : M.mem x Γ) (hy : Rd_entry_d y x R) : M.mem y Γ := by
    obtain ⟨hxX,hxU⟩ := (h.carrier x).mp hΓ
    have hyX := (mx.2.2.2 y x hy).1
    exact (h.carrier y).mpr ⟨hyX,trans ⟨x,hxX⟩ hxU ⟨y,hyX⟩ hy⟩
  have ft : M.IsSetFunctionFromTo I t Γ N := h.injection.1
  obtain ⟨E,range⟩ := ZF.exists_range_of_setFunction hZF I ft.1 ft.2.1
  have bij : M.IsSetBijectionFromTo I t Γ E := ⟨⟨⟨ft.1,ft.2.1,fun x hx =>
    (ft.2.2 x hx).imp fun y hy => ⟨(range y).mpr ⟨x,hy.2⟩,hy.2⟩⟩,h.injection.2⟩,
    fun y hy => ((range y).mp hy).imp fun x hx => ⟨ft.input_mem_of_pairMember hx,hx⟩⟩
  obtain ⟨k,back,graph⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have fk : M.IsSetInjectionFromTo I k E X := ⟨⟨back.1.1.1,back.1.1.2.1,fun x hx =>
    (back.1.1.2.2 x hx).imp fun y hy => ⟨((h.carrier y).mp hy.1).1,hy.2⟩⟩,back.1.2⟩
  refine ⟨E,k,?_,fk,?_,?_,graph⟩
  · intro x
    exact (range x).trans ⟨fun ⟨y,hy⟩ => ⟨ft.output_mem_of_pairMember hy,
      (h.image x).mpr ⟨y,ft.input_mem_of_pairMember hy,hy⟩⟩,
      fun h' => (h.image x).mp h'.2 |>.imp fun y hy => hy.2⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨x,_,pair⟩ := ft.2.2 y ((h.carrier y).mpr ⟨(mx.2.2.2 y U hy).1,hy⟩)
      exact ⟨x,(range x).mpr ⟨y,pair⟩,(graph x y).mpr pair⟩
    · rintro ⟨x,_,pair⟩
      exact ((h.carrier y).mp (ft.input_mem_of_pairMember ((graph x y).mp pair))).2
  · intro x y pair z
    have yx := (graph x y).mp pair
    constructor
    · intro hzy
      obtain ⟨v,_,zv⟩ := ft.2.2 z (down y z (ft.input_mem_of_pairMember yx) hzy)
      exact ⟨v,(h.pred y x yx v).mpr ⟨z,hzy,zv⟩,(graph v z).mpr zv⟩
    · rintro ⟨v,hvx,vz⟩
      obtain ⟨a,hay,av⟩ := (h.pred y x yx v).mp hvx
      exact h.injection.2 a z v av ((graph v z).mp vz) ▸ hay

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 共同原秩段与两侧根锚点的完整公式交换

整句真值沿共同根传输，参数沿实际共同图传输。完整低层解释的唯一性
识别这两种传输的目标值，因而任意低层原公式均保留同一个共同图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 完整低层解释沿共同图搬运，目标唯一性识别整个层对象及逐点图。 -/
theorem Ic_common_d.layer_image_l (hKP : M.Models KP)
    {X R Y S L l U V Γ t B H f K g : M.Domain}
    (common : Ic_common_d (kp_pair_l hKP) X R Y S L l U V Γ t)
    (nx : ∃ x, M.mem x X) (ext : Rf_ext_d (kp_pair_l hKP) Y S)
    (source : Rr_layer_d (kp_pair_l hKP) B X R H f)
    (target : Rr_layer_d (kp_pair_l hKP) B Y S K g)
    (trans : (smdl_structure_l (kp_pair_l hKP) (R := R) nx).TransitiveSet ⟨U,common.left_rank.2.1⟩)
    (inside : Rd_entry_d H U R) :
    Rd_entry_d H K t ∧ ∀ a y, Rd_entry_d a y g ↔ ∃ x, Rd_entry_d a x f ∧ Rd_entry_d x y t := by
  have member a x (hax : Rd_entry_d a x f) : M.mem x Γ :=
    (common.carrier x).mpr ⟨source.injection.1.output_mem_of_pairMember hax,
      trans ⟨H,source.member⟩ inside ⟨x,source.injection.1.output_mem_of_pairMember hax⟩
        ((source.image x).mpr ⟨a,source.injection.1.input_mem_of_pairMember hax,hax⟩)⟩
  obtain ⟨H',_,iH⟩ := common.injection.1.2.2 H ((common.carrier H).mpr ⟨source.member,inside⟩)
  obtain ⟨g',layer,graph⟩ := source.image_l hKP common.injection member common.pred iH
  obtain ⟨eqH,eqg⟩ := layer.unique_l hKP target ext
  exact ⟨eqH ▸ iH,eqg ▸ graph⟩

variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.anchor_peer_l
    {ω γ B r Z Q x X R y Y S π σ C₀ L l U V Γ t H f : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hω : M.IsOmega ω) (mz : Smdl_d I r Z Q) (mx : Smdl_d I x X R) (my : Smdl_d I y Y S)
    (j : Smap_d I ω r x Z X π) (k : Smap_d I ω r y Z Y σ)
    (ex : Rf_ext_d I X R) (ey : Rf_ext_d I Y S)
    (anchor : Tg_anchor_d I γ B X R π) (target : Tg_anchor_d I γ B Y S σ)
    (source : Rr_layer_d I B X R H f)
    (trans : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet ⟨U, common.left_rank.2.1⟩)
    (inside : Rd_entry_d H U R)
    (C : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := S) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet C)
    (dt : (smdl_structure_l I (R := S) my.2.1).TransitiveSet D)
    (nc : Nonempty {a : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem a C})
    (nd : Nonempty {a : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem a D})
    (iC : Rd_entry_d C₀ C.val π) (iD : Rd_entry_d C₀ D.val σ)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (ρ : Env (rt_model_l C nc) n)
    (low : ∀ i, Rd_entry_d (ρ.bound i).val.val H R) (valid : Formula.satisfies ρ φ) :
    ∃ θ : Env (rt_model_l D nd) n,
      (∀ i, Rd_entry_d (ρ.bound i).val.val (θ.bound i).val.val t) ∧ Formula.satisfies θ φ := by
  obtain ⟨θ, roots, truth⟩ := anchor.native_peer_l hZF target hω mz mx my j k ex source
    C D ct dt nc nd iC iD φ closed ρ low valid
  obtain ⟨a', V', s', t', _, targetLayer, _, fixed⟩ := target
  have graph := (common.layer_image_l (ZF.modelsKP hZF) mx.2.1 ey source targetLayer trans inside).2
  refine ⟨θ, fun i => ?_, truth⟩
  obtain ⟨a, hax, hay⟩ := roots i
  have member : M.mem (ρ.bound i).val.val Γ := (common.carrier _).mpr
    ⟨(ρ.bound i).val.property, trans ⟨H,source.member⟩ inside (ρ.bound i).val (low i)⟩
  obtain ⟨z, _, hxz⟩ := common.injection.1.2.2 (ρ.bound i).val.val member
  have point := fixed a z ((graph a z).mpr ⟨_, hax, hxz⟩)
  exact k.1.1.1.2 a z (θ.bound i).val.val point hay ▸ hxz

/-- 目标低层中的实际查询沿共同根回到源；逐点对应仍是原共同图的反向读取。 -/
theorem Ic_common_d.anchor_back_l
    {ω γ B r Z Q x X R y Y S π σ C₀ L l U V Γ t H f K g : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hω : M.IsOmega ω) (mz : Smdl_d I r Z Q) (mx : Smdl_d I x X R) (my : Smdl_d I y Y S)
    (j : Smap_d I ω r x Z X π) (k : Smap_d I ω r y Z Y σ)
    (ex : Rf_ext_d I X R) (ey : Rf_ext_d I Y S)
    (anchor : Tg_anchor_d I γ B X R π) (target : Tg_anchor_d I γ B Y S σ)
    (source : Rr_layer_d I B X R H f) (next : Rr_layer_d I B Y S K g)
    (trans : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet ⟨U,common.left_rank.2.1⟩)
    (inside : Rd_entry_d H U R)
    (C : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (D : (smdl_structure_l I (R := S) my.2.1).Domain)
    (ct : (smdl_structure_l I (R := R) mx.2.1).TransitiveSet C)
    (dt : (smdl_structure_l I (R := S) my.2.1).TransitiveSet D)
    (nc : Nonempty {a : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem a C})
    (nd : Nonempty {a : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem a D})
    (iC : Rd_entry_d C₀ C.val π) (iD : Rd_entry_d C₀ D.val σ)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (ρ : Env (rt_model_l D nd) n)
    (low : ∀ i, Rd_entry_d (ρ.bound i).val.val K S) (valid : Formula.satisfies ρ φ) :
    ∃ θ : Env (rt_model_l C nc) n,
      (∀ i, Rd_entry_d (θ.bound i).val.val (ρ.bound i).val.val t) ∧ Formula.satisfies θ φ := by
  obtain ⟨θ,roots,truth⟩ := target.native_peer_l hZF anchor hω mz my mx k j ey next
    D C dt ct nd nc iD iC φ closed ρ low valid
  have graph := (common.layer_image_l (ZF.modelsKP hZF) mx.2.1 ey source next trans inside).2
  obtain ⟨a,V₀,s,t₀,_,layer,_,fixed⟩ := anchor
  have eq := (source.unique_l (ZF.modelsKP hZF) layer ex).2
  refine ⟨θ,fun i => ?_,truth⟩
  obtain ⟨a,ha,haθ⟩ := roots i
  obtain ⟨b,hab,hb⟩ := (graph a (ρ.bound i).val.val).mp ha
  exact j.1.1.1.2 a b (θ.bound i).val.val (fixed a b (eq ▸ hab)) haθ ▸ hb

end YesMetaZFC.SetTheory.LargeCardinal
