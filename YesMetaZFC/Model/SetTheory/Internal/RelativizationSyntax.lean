import YesMetaZFC.Model.SetTheory.Internal.RelativizationRule
import YesMetaZFC.Model.SetTheory.Internal.Support
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.SetTheory.Notation

/-! # 全部内部程序的限制翻译

新变量 b 指向被限制的载体。语义只要求旧关系是新关系在该载体上的限制，
且新关系通过指定对象正确读取这个载体的成员；任意实际隶属子结构都满足这些最弱条件。
翻译状态保存已经处理的各行，不要求内部程序有外部有限长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Sr_context_d (ω X R Y S H E D : M.Domain) : Prop where
  subset : M.MemberSubset X Y
  relation : ∀ x y, M.mem x X → M.mem y X → (M.PairMember I x y R ↔ M.PairMember I x y S)
  guard : ∀ x, M.mem x Y → (M.PairMember I x H S ↔ M.mem x X)
  small : M.IsFunctionSpace I E ω X
  large : M.IsFunctionSpace I D ω Y

def sr_context_m {d} (ω X R Y S H E D : Term d) : Formula 1 d := set[d] ⟪
  ⌜X⌝ₛ ⊆ ⌜Y⌝ₛ ∧
  (∀ x y, x ∈ ⌜X⌝ₛ → y ∈ ⌜X⌝ₛ →
    (⌜Formula.orderedPairMem 𝒞⌝ₚ(x, y, ⌜R⌝ₛ) ↔ ⌜Formula.orderedPairMem 𝒞⌝ₚ(x, y, ⌜S⌝ₛ))) ∧
  (∀ x, x ∈ ⌜Y⌝ₛ → (⌜Formula.orderedPairMem 𝒞⌝ₚ(x, ⌜H⌝ₛ, ⌜S⌝ₛ) ↔ x ∈ ⌜X⌝ₛ)) ∧
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(⌜E⌝ₛ, ⌜ω⌝ₛ, ⌜X⌝ₛ) ∧
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(⌜D⌝ₛ, ⌜ω⌝ₛ, ⌜Y⌝ₛ)⟫

@[simp] theorem sr_context_closed_l {d} (ω X R Y S H E D : Term d)
    (hω : ω.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hY : Y.freeSupport = []) (hS : S.freeSupport = []) (hH : H.freeSupport = []) (hE : E.freeSupport = []) (hD : D.freeSupport = []) :
    (sr_context_m (𝒞 := 𝒞) ω X R Y S H E D).FreeClosed := by
  simp -implicitDefEqProofs [sr_context_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed,
    hω, hX, hR, hY, hS, hH, hE, hD]

theorem sr_context_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R Y S H E D : Term d) :
    Formula.satisfies ρ (sr_context_m (𝒞 := 𝒞) ω X R Y S H E D) ↔
      Sr_context_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (Y.eval ρ) (S.eval ρ) (H.eval ρ) (E.eval ρ) (D.eval ρ) := by
  simp only [sr_context_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_isFunctionSpace_iff I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.subset, h.relation, h.guard, h.small, h.large⟩⟩

theorem sr_context_l {ω c X R d Y S E D : M.Domain} (hx : Smem_d I c X R) (hy : Smem_d I d Y S)
    (hXY : M.MemberSubset X Y) (hX : M.mem X Y) (hE : M.IsFunctionSpace I E ω X)
    (hD : M.IsFunctionSpace I D ω Y) : Sr_context_d I ω X R Y S X E D := by
  refine ⟨hXY, fun x y hxX hyX => ?_, fun x hxY => ?_, hE, hD⟩
  · exact (hx.2 x y).trans ⟨fun h => (hy.2 x y).mpr ⟨hXY x hxX, hXY y hyX, h.2.2⟩,
      fun h => ⟨hxX, hyX, ((hy.2 x y).mp h).2.2⟩⟩
  · exact (hy.2 x X).trans ⟨fun h => h.2.2, fun h => ⟨hxY, hX, h⟩⟩

def Sr_row_d (b X R Y S H E D F n m G r u : M.Domain) : Prop := ∀ f g,
  M.mem f E → M.mem g D → M.PairMember I b H g → Senv_agree_d I b f g →
    (Ssat_d I X R E F n r f ↔ Ssat_d I Y S D G m u g)

def sr_row_m {d} (b X R Y S H E D F n m G r u : Term d) : Formula 1 d := set[d] ⟪
  ∀ f g, f ∈ ⌜E⌝ₛ → g ∈ ⌜D⌝ₛ → ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜b⌝ₛ, ⌜H⌝ₛ, g) →
    ⌜senv_agree_m (𝒞 := 𝒞)⌝ₚ(⌜b⌝ₛ, f, g) →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, ⌜E⌝ₛ, ⌜F⌝ₛ, ⌜n⌝ₛ, ⌜r⌝ₛ, f) ↔
     ⌜ssat_m (𝒞 := 𝒞)⌝ₚ(⌜Y⌝ₛ, ⌜S⌝ₛ, ⌜D⌝ₛ, ⌜G⌝ₛ, ⌜m⌝ₛ, ⌜u⌝ₛ, g))⟫
derive_free_closed sr_row_m

theorem sr_row_sat_l (hE : Extensional M) {d} (ρ : Env M d) (b X R Y S H E D F n m G r u : Term d) :
    Formula.satisfies ρ (sr_row_m (𝒞 := 𝒞) b X R Y S H E D F n m G r u) ↔
      Sr_row_d I (b.eval ρ) (X.eval ρ) (R.eval ρ) (Y.eval ρ) (S.eval ρ) (H.eval ρ) (E.eval ρ) (D.eval ρ)
        (F.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (r.eval ρ) (u.eval ρ) := by
  simp only [sr_row_m, Sr_row_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, senv_agree_sat_l I,
    Formula.satisfies_iff_iff, ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

structure Sr_state_d (ω b F k m G T : M.Domain) : Prop where
  program : Sfm_d I ω m G
  map : M.IsSetFunctionFromTo I T k m
  rules : ∀ r c u, M.PairMember I r c F → M.PairMember I r u T → Sr_rule_d I b T G c u

def sr_state_m {d} (ω b F k m G T : Term d) : Formula 1 d := set[d] ⟪
  ⌜sfm_m (𝒞 := 𝒞)⌝ₚ(⌜ω⌝ₛ, ⌜m⌝ₛ, ⌜G⌝ₛ) ∧
  ⌜Formula.isFunctionFromTo 𝒞⌝ₚ(⌜T⌝ₛ, ⌜k⌝ₛ, ⌜m⌝ₛ) ∧
  (∀ r c u, ⌜Formula.orderedPairMem 𝒞⌝ₚ(r, c, ⌜F⌝ₛ) → ⌜Formula.orderedPairMem 𝒞⌝ₚ(r, u, ⌜T⌝ₛ) →
    ⌜sr_rule_m (𝒞 := 𝒞)⌝ₚ(⌜b⌝ₛ, ⌜T⌝ₛ, ⌜G⌝ₛ, c, u))⟫
derive_free_closed sr_state_m

theorem sr_state_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω b F k m G T : Term d) :
    Formula.satisfies ρ (sr_state_m (𝒞 := 𝒞) ω b F k m G T) ↔
      Sr_state_d I (ω.eval ρ) (b.eval ρ) (F.eval ρ) (k.eval ρ) (m.eval ρ) (G.eval ρ) (T.eval ρ) := by
  simp only [sr_state_m, Formula.satisfies_conj_iff, sfm_sat_l I hE, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I, sr_rule_sat_l I, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.program, h.map, h.rules⟩⟩

theorem Sr_state_d.extend_l {ω b F k m G T l H z : M.Domain}
    (h : Sr_state_d I ω b F k m G T) (e : Sbuild_d I ω m G l H z) : Sr_state_d I ω b F k l H T := by
  refine ⟨e.program, ⟨h.map.1, h.map.2.1, fun i hi => ?_⟩, fun r c u hc hu => ?_⟩
  · obtain ⟨u, hu, hiu⟩ := h.map.2.2 i hi
    exact ⟨u, e.span u hu, hiu⟩
  · exact (h.rules r c u hc hu).mono_l I (fun _ _ h => h) (fun i j h => ((e.cut.2 i j).mp h).2)

end YesMetaZFC.SetTheory.Internal
