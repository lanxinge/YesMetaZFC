import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.Model.SetTheory.Source.CollectionBasis
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.Model.SetTheory.LevyReflection.Bounded
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.KP.TransitiveInduction
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift

/-! # 共同低层实现图的有界公式保持

完整前驱方程把原关系中的有界量词见证回收到同一实际低层。
因此函数、求值和复合都按原固定公式传输，无须先塌缩整个关系模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rr_realize_delta_l {Γ Y S k : M.Domain} (hΓ : M.TransitiveSet Γ)
    (nx : Nonempty {x // M.mem x Γ}) (ny : ∃ y, M.mem y Y)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x a, M.PairMember I x a k → ∀ b,
      M.PairMember I b a S ↔ ∃ y, M.mem y x ∧ M.PairMember I y b k)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (delta : φ.IsDelta0)
    (ρ : Env (rt_model_l Γ nx) n) (η : Env (smdl_structure_l I (R := S) ny) n)
    (params : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val k) :
    Formula.satisfies (image_env_l Subtype.val ρ) φ ↔ Formula.satisfies η φ := by
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun x : {x // M.mem x Γ} => fk.1.2.2 x.val x.property)
  let e : (rt_model_l Γ nx).Domain → (smdl_structure_l I (R := S) ny).Domain := fun x => ⟨f x, (hf x).1⟩
  have injective : Function.Injective e := by
    intro x y eq
    have eq : f x = f y := congrArg Subtype.val eq
    exact Subtype.ext (fk.2 x.val y.val (f y) (eq ▸ (hf x).2) (hf y).2)
  have member (a : (rt_model_l Γ nx).Domain) (b : (smdl_structure_l I (R := S) ny).Domain) :
      (smdl_structure_l I (R := S) ny).mem b (e a) ↔
        ∃ x : (rt_model_l Γ nx).Domain, (rt_model_l Γ nx).mem x a ∧ e x = b := by
    apply (pred a.val (f a) (hf a).2 b.val).trans
    exact ⟨fun ⟨x, hx, hxb⟩ => ⟨⟨x, hΓ a.val a.property x hx⟩, hx,
      Subtype.ext (fk.1.1.2 x _ b.val (hf ⟨x, hΓ a.val a.property x hx⟩).2 hxb)⟩,
      fun ⟨x, hx, eq⟩ => ⟨x.val, hx, congrArg Subtype.val eq ▸ (hf x).2⟩⟩
  apply (rt_model_delta_l hΓ nx delta ρ).symm.trans ((delta0_image_l e injective member delta ρ).trans ?_)
  exact Formula.closed_env_l φ closed (funext fun i =>
    Subtype.ext (fk.1.1.2 _ _ _ (hf (ρ.bound i)).2 (params i)))

theorem rr_realize_function_l (hM : Extensional M) {Γ Y S k D E t : M.Domain}
    (hΓ : M.TransitiveSet Γ) (ny : ∃ y, M.mem y Y) (ext : Rf_ext_d I Y S)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x a, M.PairMember I x a k → ∀ b,
      M.PairMember I b a S ↔ ∃ y, M.mem y x ∧ M.PairMember I y b k)
    (d e p : (smdl_structure_l I (R := S) ny).Domain)
    (hD : M.PairMember I D d.val k) (hE : M.PairMember I E e.val k) (ht : M.PairMember I t p.val k)
    (ft : Fn0_d E D t) : Fn0_d e d p ∧ ∀ s r x y,
      Rd_entry_d s r t → M.PairMember I s x k → M.PairMember I r y k → Rf_val_d I Y S x y p.val := by
  let nx : Nonempty {x // M.mem x Γ} := ⟨⟨D, fk.1.input_mem_of_pairMember hD⟩⟩
  let D' : (rt_model_l Γ nx).Domain := ⟨D, fk.1.input_mem_of_pairMember hD⟩
  let E' : (rt_model_l Γ nx).Domain := ⟨E, fk.1.input_mem_of_pairMember hE⟩
  let t' : (rt_model_l Γ nx).Domain := ⟨t, fk.1.input_mem_of_pairMember ht⟩
  have en := ext.native_l I ny
  have transfer := rr_realize_delta_l I hΓ nx ny fk pred (fn0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fn0_delta_l ..)
    (⟨Fin.cases t' (Fin.cases D' (fun _ => E')), fun _ => D'⟩ : Env (rt_model_l Γ nx) 3)
    (⟨Fin.cases p (Fin.cases d (fun _ => e)), fun _ => d⟩ : Env (smdl_structure_l I (R := S) ny) 3)
    (Fin.cases ht (Fin.cases hD (fun _ => hE)))
  refine ⟨(fn0_sat_l en ..).mp (transfer.mp ((fn0_sat_l hM ..).mpr ft)), fun s r x y hsr hsx hry => ?_⟩
  let s' : (rt_model_l Γ nx).Domain := ⟨s, fk.1.input_mem_of_pairMember hsx⟩
  let r' : (rt_model_l Γ nx).Domain := ⟨r, fk.1.input_mem_of_pairMember hry⟩
  let x' : (smdl_structure_l I (R := S) ny).Domain := ⟨x, fk.1.output_mem_of_pairMember hsx⟩
  let y' : (smdl_structure_l I (R := S) ny).Domain := ⟨y, fk.1.output_mem_of_pairMember hry⟩
  have read := rr_realize_delta_l I hΓ nx ny fk pred (rd_entry0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    (⟨Fin.cases t' (Fin.cases r' (fun _ => s')), fun _ => D'⟩ : Env (rt_model_l Γ nx) 3)
    (⟨Fin.cases p (Fin.cases y' (fun _ => x')), fun _ => d⟩ : Env (smdl_structure_l I (R := S) ny) 3)
    (Fin.cases ht (Fin.cases hry (fun _ => hsx)))
  exact (rf_val_native_l I ny en x' y' p).mpr
    ((rd_entry0_sat_l en ..).mp (read.mp ((rd_entry0_sat_l hM ..).mpr hsr)))

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系低层的内在闭包

小性与子集封闭直接量化当前关系模型的全部对象。初等过渡保持这两条
原句，因此递归中新出现的低层无需是最初传递源中某个对象的像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rr_closed_d (Y S H : M.Domain) : Prop := ∀ a b, M.mem a Y → M.mem b Y →
  M.PairMember I a H S → (∀ x, M.mem x Y → M.PairMember I x b S → M.PairMember I x a S) → M.PairMember I b H S

def Rr_small_d (Y S H : M.Domain) : Prop := ∀ a, M.mem a Y → M.PairMember I a H S → Rf_small_d I Y S a

def rr_closed_m : Formula 1 1 := Formula.forallMem .newest (.forallE
  (.imp (Formula.subset .newest (.bound 1)) (.mem .newest (.bound 2))))

def rr_small_m : Formula 1 1 := Formula.forallMem .newest (sc_small_m .newest)
derive_free_closed rr_closed_m
derive_free_closed rr_small_m

theorem rr_closed_native_l {Y S} (ny : ∃ y, M.mem y Y) (H : (smdl_structure_l I (R := S) ny).Domain) :
    Formula.satisfies (⟨fun _ => H, fun _ => H⟩ : Env (smdl_structure_l I (R := S) ny) 1) rr_closed_m ↔
      Rr_closed_d I Y S H.val := by
  simp only [rr_closed_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Formula.satisfies_mem_iff]
  exact ⟨fun h a b ha hb haH sub => h ⟨a, ha⟩ haH ⟨b, hb⟩ (fun x => sub x.val x.property),
    fun h a ha b sub => h a.val b.val a.property b.property ha (fun x hx => sub ⟨x, hx⟩)⟩

theorem rr_small_native_l {Y S} (ny : ∃ y, M.mem y Y) (H : (smdl_structure_l I (R := S) ny).Domain) :
    Formula.satisfies (⟨fun _ => H, fun _ => H⟩ : Env (smdl_structure_l I (R := S) ny) 1) rr_small_m ↔
      Rr_small_d I Y S H.val := by
  rw [rr_small_m, Formula.satisfies_forallMem_iff]
  exact ⟨fun h a ha haH => ⟨ha, h ⟨a, ha⟩ haH⟩,
    fun h a ha => (h a.val a.property ha).elim fun _ valid => valid⟩

theorem Smap_d.rr_closed_l (hZF : M.Models ZF) {ω c Y S o C W j H H' : M.Domain}
    (hω : M.IsOmega ω) (my : Smdl_d I c Y S) (mc : Smdl_d I o C W)
    (hj : Smap_d I ω c o Y C j) (hH : M.PairMember I H H' j) :
    Rr_closed_d I Y S H ↔ Rr_closed_d I C W H' := by
  let a : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨H, hj.1.1.input_mem_of_pairMember hH⟩
  let b : (smdl_structure_l I (R := W) mc.2.1).Domain := ⟨H', hj.1.1.output_mem_of_pairMember hH⟩
  exact (rr_closed_native_l I my.2.1 a).symm.trans
    ((smap_source_l I hZF hω my mc hj rr_closed_m
      (by simp -implicitDefEqProofs [rr_closed_m, Formula.forallMem, Definitional.Formula.FreeClosed])
      ⟨fun _ => a, fun _ => a⟩ ⟨fun _ => b, fun _ => b⟩ (fun _ => hH)).trans (rr_closed_native_l I mc.2.1 b))

theorem Smap_d.rr_small_l (hZF : M.Models ZF) {ω c Y S o C W j H H' : M.Domain}
    (hω : M.IsOmega ω) (my : Smdl_d I c Y S) (mc : Smdl_d I o C W)
    (hj : Smap_d I ω c o Y C j) (hH : M.PairMember I H H' j) :
    Rr_small_d I Y S H ↔ Rr_small_d I C W H' := by
  let a : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨H, hj.1.1.input_mem_of_pairMember hH⟩
  let b : (smdl_structure_l I (R := W) mc.2.1).Domain := ⟨H', hj.1.1.output_mem_of_pairMember hH⟩
  exact (rr_small_native_l I my.2.1 a).symm.trans
    ((smap_source_l I hZF hω my mc hj rr_small_m (by simp -implicitDefEqProofs [rr_small_m])
      ⟨fun _ => a, fun _ => a⟩ ⟨fun _ => b, fun _ => b⟩ (fun _ => hH)).trans (rr_small_native_l I mc.2.1 b))

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系模型中共同低层的完整解释

只实现指定传递层的全部成员和全部前驱。高层载体可以尚未坍塌；全公式的
量词在该层内解释，不能把高层对象码当成背景集合来读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Rr_layer_d (Γ Y S H k : M.Domain) : Prop where
  transitive : M.TransitiveSet Γ
  member : M.mem H Y
  injection : M.IsSetInjectionFromTo I k Γ Y
  image : ∀ z, M.PairMember I z H S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x z k
  predecessors : ∀ x z, M.PairMember I x z k → ∀ w,
    M.PairMember I w z S ↔ ∃ y, M.mem y x ∧ M.PairMember I y w k

def rr_layer_m {d} (Γ Y S H k : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isTransitive⌝ₚ(⌜Γ⌝ₛ) ∧ ⌜H⌝ₛ ∈ ⌜Y⌝ₛ ∧
  ⌜Formula.isInjectionFromTo kpair_convention_l⌝ₚ(⌜k⌝ₛ, ⌜Γ⌝ₛ, ⌜Y⌝ₛ) ∧
  (∀ x, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(x, ⌜H⌝ₛ, ⌜S⌝ₛ) ↔
    ∃ n ∈ ⌜Γ⌝ₛ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(n, x, ⌜k⌝ₛ)) ∧
  (∀ n x, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(n, x, ⌜k⌝ₛ) →
    ∀ y, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(y, x, ⌜S⌝ₛ) ↔
      ∃ m ∈ n, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(m, y, ⌜k⌝ₛ))⟫
derive_free_closed rr_layer_m

theorem rr_layer_sat_l (hE : Extensional M) {d} (ρ : Env M d) (Γ Y S H k : Term d) :
    Formula.satisfies ρ (rr_layer_m Γ Y S H k) ↔
      Rr_layer_d I (Γ.eval ρ) (Y.eval ρ) (S.eval ρ) (H.eval ρ) (k.eval ρ) := by
  simp only [rr_layer_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isInjectionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨t,h,f,i,p⟩ => ⟨t,h,f,i,p⟩, fun h => ⟨h.transitive,h.member,h.injection,h.image,h.predecessors⟩⟩

/-- 完整前驱解释把任意背景序数读成原关系中的有界序数公式。 -/
theorem Rr_layer_d.ordinal_l (hE : Extensional M) {Γ Y R H k : M.Domain}
    (hΓ : M.IsOrdinal Γ) (layer : Rr_layer_d I Γ Y R H k) :
    Rr_truth_d I Y R (KP.ord0_m .newest) (fun _ : Fin 1 => H) := by
  let N := smdl_structure_l I (R := R) ⟨H, layer.member⟩
  have trans : N.TransitiveSet ⟨H, layer.member⟩ := by
    intro x hx y hy
    obtain ⟨n, hn, hnx⟩ := (layer.image x.val).mp hx
    obtain ⟨m, hm, hmy⟩ := (layer.predecessors n x.val hnx y.val).mp hy
    exact (layer.image y.val).mpr ⟨m, hΓ.transitive n hn m hm, hmy⟩
  have members (x : N.Domain) (hx : N.mem x ⟨H, layer.member⟩) : N.TransitiveSet x := by
    obtain ⟨n, hn, hnx⟩ := (layer.image x.val).mp hx
    intro y hy z hz
    obtain ⟨m, hm, hmy⟩ := (layer.predecessors n x.val hnx y.val).mp hy
    obtain ⟨l, hl, hlz⟩ := (layer.predecessors m y.val hmy z.val).mp hz
    exact (layer.predecessors n x.val hnx z.val).mpr ⟨l, (hΓ.mem hn).transitive m hm l hl, hlz⟩
  have compare (x : N.Domain) (hx : N.mem x ⟨H, layer.member⟩)
      (y : N.Domain) (hy : N.mem y ⟨H, layer.member⟩) : N.SameMembers x y ∨ N.mem x y ∨ N.mem y x := by
    obtain ⟨n, hn, hnx⟩ := (layer.image x.val).mp hx
    obtain ⟨m, hm, hmy⟩ := (layer.image y.val).mp hy
    rcases hΓ.wellOrder.linear.compare n hn m hm with eq | lt | gt
    · have eq := hE.eq_of_same_members n m eq
      subst m
      have eq : x = y := Subtype.ext (layer.injection.1.1.2 n x.val y.val hnx hmy)
      exact Or.inl (eq ▸ fun _ => Iff.rfl)
    · exact Or.inr (Or.inl ((layer.predecessors m y.val hmy x.val).mpr ⟨n, lt, hnx⟩))
    · exact Or.inr (Or.inr ((layer.predecessors n x.val hnx y.val).mpr ⟨m, gt, hmy⟩))
  apply (rr_truth_native_l I ⟨H, layer.member⟩ _ (by simp -implicitDefEqProofs) (fun _ => ⟨H, layer.member⟩)).mpr
  simp only [KP.ord0_m, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨trans, members, compare⟩

/-- 用实际限制图实现任意传递子层；新层的成员方程就是原前驱方程。 -/
theorem Rr_layer_d.restrict_l (hZF : M.Models ZF) {Γ Y S H k B b : M.Domain}
    (h : Rr_layer_d I Γ Y S H k) (trans : M.TransitiveSet B) (image : M.PairMember I B b k) :
    ∃ t, Rr_layer_d I B Y S b t ∧ M.IsRestrictionOf I t k B := by
  have inside := h.transitive B (h.injection.1.input_mem_of_pairMember image)
  obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I k B
  refine ⟨t, ⟨trans, h.injection.1.output_mem_of_pairMember image,
    ⟨ht.isSetFunctionFromTo h.injection.1 inside, fun x y z hx hy =>
      h.injection.2 x y z ((ht.2 x z).mp hx).2 ((ht.2 y z).mp hy).2⟩, ?_, ?_⟩, ht⟩
  · intro z
    apply (h.predecessors B b image z).trans
    exact exists_congr fun x => and_congr_right fun hx =>
      ⟨fun e => (ht.2 x z).mpr ⟨hx, e⟩, fun e => ((ht.2 x z).mp e).2⟩
  · intro x z hx w
    obtain ⟨hxB, hxz⟩ := (ht.2 x z).mp hx
    apply (h.predecessors x z hxz w).trans
    exact exists_congr fun y => and_congr_right fun hy =>
      ⟨fun e => (ht.2 y w).mpr ⟨trans x hxB y hy, e⟩, fun e => ((ht.2 y w).mp e).2⟩

section Image
variable (hKP : M.Models KP)
local notation "Kp" => kp_pair_l hKP

/-- 完整前驱图搬运同一个传递层；复合的中间值仍是原对象码。 -/
theorem Rr_layer_d.image_l {Γ X R H z D Y S t K : M.Domain}
    (h : Rr_layer_d Kp Γ X R H z) (ft : M.IsSetInjectionFromTo Kp t D Y)
    (inside : ∀ a x, M.PairMember Kp a x z → M.mem x D)
    (pred : ∀ x y, M.PairMember Kp x y t → ∀ v,
      M.PairMember Kp v y S ↔ ∃ s, M.PairMember Kp s x R ∧ M.PairMember Kp s v t)
    (hHK : M.PairMember Kp H K t) :
    ∃ q, Rr_layer_d Kp Γ Y S K q ∧ ∀ a y,
      M.PairMember Kp a y q ↔ ∃ x, M.PairMember Kp a x z ∧ M.PairMember Kp x y t := by
  have fz : M.IsSetFunctionFromTo Kp z Γ D :=
    ⟨h.injection.1.1, h.injection.1.2.1, fun a ha =>
      (h.injection.1.2.2 a ha).imp fun x hx => ⟨inside a x hx.2, hx.2⟩⟩
  have fz' := fn0_of_function_l hKP fz
  have ft' := fn0_of_function_l hKP ft.1
  obtain ⟨q, comp⟩ := cp0_exists_l hKP fz' ft'
  have fq := fn0_function_l hKP comp.1
  have graph a y : M.PairMember Kp a y q ↔ ∃ x, M.PairMember Kp a x z ∧ M.PairMember Kp x y t := by
    constructor
    · intro hay
      obtain ⟨x, _, hax⟩ := fz.2.2 a (fq.input_mem_of_pairMember hay)
      exact ⟨x, hax, (comp.value_l fz' ft' hax).mp hay⟩
    · rintro ⟨x, hax, hxy⟩
      exact (comp.value_l fz' ft' hax).mpr hxy
  have injective : M.IsSetInjective Kp q := by
    intro a b y ha hb
    obtain ⟨x, hx, hxy⟩ := (graph a y).mp ha
    obtain ⟨v, hv, hvy⟩ := (graph b y).mp hb
    exact h.injection.2 a b x hx (ft.2 v x y hvy hxy ▸ hv)
  refine ⟨q, ⟨h.transitive, ft.1.output_mem_of_pairMember hHK, ⟨fq, injective⟩, ?_, ?_⟩, graph⟩
  · intro y
    apply (pred H K hHK y).trans
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨a, ha, hax⟩ := (h.image x).mp hx
      exact ⟨a, ha, (graph a y).mpr ⟨x, hax, hxy⟩⟩
    · rintro ⟨a, ha, hay⟩
      obtain ⟨x, hax, hxy⟩ := (graph a y).mp hay
      exact ⟨x, (h.image x).mpr ⟨a, ha, hax⟩, hxy⟩
  · intro a y hay v
    obtain ⟨x, hax, hxy⟩ := (graph a y).mp hay
    apply (pred x y hxy v).trans
    constructor
    · rintro ⟨s, hs, hsv⟩
      obtain ⟨b, hb, hbs⟩ := (h.predecessors a x hax s).mp hs
      exact ⟨b, hb, (graph b v).mpr ⟨s, hbs, hsv⟩⟩
    · rintro ⟨b, hb, hbv⟩
      obtain ⟨s, hbs, hsv⟩ := (graph b v).mp hbv
      exact ⟨s, (h.predecessors a x hax s).mpr ⟨b, hb, hbs⟩, hsv⟩

end Image

/-- 原隶属模型的实际低层以恒等限制图实现，作为生产调用的初始实例。 -/
theorem rr_layer_mem_l (hZF : M.Models ZF) {c Y S Γ : M.Domain} (model : Smem_d I c Y S)
    (hY : M.TransitiveSet Y) (hΓ : M.mem Γ Y) (trans : M.TransitiveSet Γ) :
    ∃ k, Rr_layer_d I Γ Y S Γ k ∧ ∀ x y, M.PairMember I x y k ↔ M.mem x Γ ∧ x = y := by
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => Γ⟩
  have read x y : φ.denote ρ x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨k, fn, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ
    (source := Γ) (target := Y) (fun x _ => ⟨x, (read x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((read x y).mp hy).symm.trans ((read x z).mp hz))
    (fun x y hx hy => (read x y).mp hy ▸ hY Γ hΓ x hx)
  have graph x y : M.PairMember I x y k ↔ M.mem x Γ ∧ x = y :=
    (spec x y).trans (and_congr Iff.rfl (read x y))
  refine ⟨k, ⟨trans, hΓ, ⟨fn, fun x y z hx hy => ((graph x z).mp hx).2.trans ((graph y z).mp hy).2.symm⟩, ?_, ?_⟩, graph⟩
  · intro z
    apply (model.2 z Γ).trans
    exact ⟨fun h => ⟨z, h.2.2, (graph z z).mpr ⟨h.2.2, rfl⟩⟩,
      fun ⟨x, hx, hz⟩ => ((graph x z).mp hz).2 ▸ ⟨hY Γ hΓ x hx, hΓ, hx⟩⟩
  · intro x z hz w
    obtain ⟨hx, rfl⟩ := (graph x z).mp hz
    apply (model.2 w x).trans
    exact ⟨fun h => ⟨w, h.2.2, (graph w w).mpr ⟨trans x hx w h.2.2, rfl⟩⟩,
      fun ⟨y, hy, hw⟩ => ((graph y w).mp hw).2 ▸ ⟨hY Γ hΓ y (trans x hx y hy), hY Γ hΓ x hx, hy⟩⟩

/-- 全量词相对化与低层原真值等价；前驱满性同时处理两个定义原子。 -/
theorem Rr_layer_d.relative_l {Γ Y S H k : M.Domain} (h : Rr_layer_d I Γ Y S H k)
    (nc : Nonempty {x // M.mem x Γ}) {n d} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l Γ nc) n) (η : Env (smdl_structure_l I (R := S) ⟨H, h.member⟩) d)
    (T : Term d) (a : Fin n → Term d) (hT : (T.eval η).val = H)
    (params : ∀ i, M.PairMember I (ρ.bound i).val ((a i).eval η).val k) :
    Formula.satisfies ρ φ ↔ Formula.satisfies η (lr_rel_m φ T a) := by
  have term {n d} (ρ : Env (rt_model_l Γ nc) n)
      (η : Env (smdl_structure_l I (R := S) ⟨H, h.member⟩) d) (a : Fin n → Term d)
      (ha : ∀ i, M.PairMember I (ρ.bound i).val ((a i).eval η).val k)
      (t : Term n) (ht : t.freeSupport = []) : M.PairMember I (t.eval ρ).val ((t.bind a).eval η).val k := by
    cases t with
    | free _ => cases ht
    | bound i => exact ha i
  have mem (x y : (rt_model_l Γ nc).Domain)
      (v w : (smdl_structure_l I (R := S) ⟨H, h.member⟩).Domain)
      (hx : M.PairMember I x.val v.val k) (hy : M.PairMember I y.val w.val k) :
      M.mem x.val y.val ↔ M.PairMember I v.val w.val S :=
    ⟨fun e => (h.predecessors y.val w.val hy v.val).mpr ⟨x.val, e, hx⟩,
      fun e => ((h.predecessors y.val w.val hy v.val).mp e).elim fun z hz =>
        h.injection.2 z x.val v.val hz.2 hx ▸ hz.1⟩
  have sub (x y : (rt_model_l Γ nc).Domain)
      (v w : (smdl_structure_l I (R := S) ⟨H, h.member⟩).Domain)
      (hx : M.PairMember I x.val v.val k) (hy : M.PairMember I y.val w.val k) :
      (rt_model_l Γ nc).MemberSubset x y ↔ (smdl_structure_l I (R := S) ⟨H, h.member⟩).MemberSubset v w := by
    constructor
    · intro hs z hz
      obtain ⟨b, hb, hbk⟩ := (h.predecessors x.val v.val hx z.val).mp hz
      exact (mem ⟨b, h.transitive x.val x.property b hb⟩ y z w hbk hy).mp
        (hs ⟨b, h.transitive x.val x.property b hb⟩ hb)
    · intro hs z hz
      obtain ⟨b, hb, hzb⟩ := h.injection.1.2.2 z.val z.property
      exact (mem z y ⟨b, hb⟩ w hzb hy).mpr (hs ⟨b, hb⟩ ((mem z x ⟨b, hb⟩ v hzb hx).mp hz))
  have equal (x y : (rt_model_l Γ nc).Domain)
      (v w : (smdl_structure_l I (R := S) ⟨H, h.member⟩).Domain)
      (hx : M.PairMember I x.val v.val k) (hy : M.PairMember I y.val w.val k) :
      (rt_model_l Γ nc).SameMembers x y ↔ (smdl_structure_l I (R := S) ⟨H, h.member⟩).SameMembers v w :=
    ⟨fun hs z => ⟨(sub x y v w hx hy).mp (fun b => (hs b).mp) z,
      (sub y x w v hy hx).mp (fun b => (hs b).mpr) z⟩,
      fun hs z => ⟨(sub x y v w hx hy).mpr (fun b => (hs b).mp) z,
        (sub y x w v hy hx).mpr (fun b => (hs b).mpr) z⟩⟩
  induction φ generalizing d <;> simp only [Definitional.Formula.FreeClosed] at closed
  case falsum | truth => rfl
  case mem s t => exact mem _ _ _ _ (term ρ η a params s closed.1) (term ρ η a params t closed.2)
  case atom r hr ts =>
    cases r <;> simp only [lr_rel_m, Formula.satisfies_atom_extensionalEq_iff,
      Formula.satisfies_atom_subset_iff, Definitional.TermVector.get_bind]
    · exact equal _ _ _ _ (term ρ η a params (ts 0) (closed 0)) (term ρ η a params (ts 1) (closed 1))
    · exact sub _ _ _ _ (term ρ η a params (ts 0) (closed 0)) (term ρ η a params (ts 1) (closed 1))
  case neg φ ih => exact not_congr (ih closed ρ η T a hT params)
  case conj φ ψ ih jh => exact and_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case disj φ ψ ih jh => exact or_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case imp φ ψ ih jh => exact imp_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case iff φ ψ ih jh => exact iff_congr (ih closed.1 ρ η T a hT params) (jh closed.2 ρ η T a hT params)
  case existsE φ ih | forallE φ ih =>
    have next (x : (rt_model_l Γ nc).Domain) (y : (smdl_structure_l I (R := S) ⟨H, h.member⟩).Domain)
        (hy : M.PairMember I x.val y.val k) := ih closed (ρ.push x) (η.push y) T.weaken
          (Fin.cases .newest (fun i => (a i).weaken)) (by simpa using hT)
          (Fin.cases hy (fun i => by
            simp only [Fin.cases_succ, Definitional.Term.eval_weaken]
            simpa only [Env.push, fin_cases_succ] using params i))
    first
    | rw [lr_rel_m, Formula.satisfies_existsMem_iff, Formula.satisfies_exists_iff]
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨y, hy, hxy⟩ := h.injection.1.2.2 x.val x.property
        refine ⟨⟨y, hy⟩, ?_, (next x ⟨y, hy⟩ hxy).mp hx⟩
        change M.PairMember I y (T.eval η).val S
        rw [hT]
        exact (h.image y).mpr ⟨x.val, x.property, hxy⟩
      · rintro ⟨y, hy, truth⟩
        change M.PairMember I y.val (T.eval η).val S at hy
        rw [hT] at hy
        obtain ⟨x, hx, hxy⟩ := (h.image y.val).mp hy
        exact ⟨⟨x, hx⟩, (next ⟨x, hx⟩ y hxy).mpr truth⟩
    | rw [lr_rel_m, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff]
      constructor
      · intro truth y hy
        change M.PairMember I y.val (T.eval η).val S at hy
        rw [hT] at hy
        obtain ⟨x, hx, hxy⟩ := (h.image y.val).mp hy
        exact (next ⟨x, hx⟩ y hxy).mp (truth ⟨x, hx⟩)
      · intro truth x
        obtain ⟨y, hy, hxy⟩ := h.injection.1.2.2 x.val x.property
        apply (next x ⟨y, hy⟩ hxy).mpr (truth ⟨y, hy⟩ ?_)
        change M.PairMember I y (T.eval η).val S
        rw [hT]
        exact (h.image y).mpr ⟨x.val, x.property, hxy⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 良基原关系的完整前驱图在重叠域上唯一

反例集合由两张实际集合图分离得到。其原关系极小元的全部前驱已有相同像，
目标外延性遂排除该反例；不使用原模型的外部良基性或额外分离公理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rf_full_overlap_l {X R D E N S f g : M.Domain}
    (wf : Wf_rel_d X R) (sub : M.MemberSubset D X)
    (ff : M.IsSetFunctionFromTo I f D N) (fg : M.IsSetFunctionFromTo I g E N)
    (downD : ∀ x y, M.mem x D → Rd_entry_d y x R → M.mem y D)
    (downE : ∀ x y, M.mem x E → Rd_entry_d y x R → M.mem y E)
    (pf : ∀ x y, Rd_entry_d x y f → ∀ z,
      Rd_entry_d z y S ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a z f)
    (pg : ∀ x y, Rd_entry_d x y g → ∀ z,
      Rd_entry_d z y S ↔ ∃ a, Rd_entry_d a x R ∧ Rd_entry_d a z g)
    (ext : Rf_ext_d I N S) :
    ∀ x y z, Rd_entry_d x y f → Rd_entry_d x z g → y = z := by
  classical
  let ρ : Env M 3 := ⟨fun i => [N,f,g].get i,fun _ => X⟩
  let φ : UnarySchema 3 := { body := set[4] ⟪
    ∃ y ∈ ⌜(.bound 1 : Term 4)⌝ₛ, ∃ z ∈ ⌜(.bound 1 : Term 4)⌝ₛ,
      ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,y,⌜(.bound 2 : Term 4)⌝ₛ) ∧
      ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,z,⌜(.bound 3 : Term 4)⌝ₛ) ∧ ¬ y = z⟫ }
  have read x : φ.denote ρ x ↔ ∃ y z, M.mem y N ∧ M.mem z N ∧
      Rd_entry_d x y f ∧ Rd_entry_d x z g ∧ y ≠ z := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      rd_entry0_sat_l hZF.1,Definitional.Term.eval_weaken]
    change (∃ y, M.mem y N ∧ ∃ z, M.mem z N ∧ Rd_entry_d x y f ∧ Rd_entry_d x z g ∧ y ≠ z) ↔ _
    exact ⟨fun ⟨y,hy,z,hz,a,b,c⟩ => ⟨y,z,hy,hz,a,b,c⟩,
      fun ⟨y,z,hy,hz,a,b,c⟩ => ⟨y,hy,z,hz,a,b,c⟩⟩
  obtain ⟨B,sep⟩ := ZF.separation_exists_d hZF φ ρ X
  have bad x : M.mem x B ↔ M.mem x X ∧ ∃ y z, M.mem y N ∧ M.mem z N ∧
      Rd_entry_d x y f ∧ Rd_entry_d x z g ∧ y ≠ z := (sep x).trans (and_congr_right fun _ => read x)
  intro x y z xy xz
  apply Classical.byContradiction
  intro ne
  have bx := (bad x).mpr ⟨sub x (ff.input_mem_of_pairMember xy),
    y,z,ff.output_mem_of_pairMember xy,fg.output_mem_of_pairMember xz,xy,xz,ne⟩
  obtain ⟨a,ha,minimal⟩ := wf B (fun x hx => ((bad x).mp hx).1) ⟨x,bx⟩
  obtain ⟨_,b,c,hb,hc,ab,ac,neq⟩ := (bad a).mp ha
  have same {v p q : M.Domain} (va : Rd_entry_d v a R)
      (vp : Rd_entry_d v p f) (vq : Rd_entry_d v q g) : p = q := by
    apply Classical.byContradiction
    intro ne
    exact minimal v ((bad v).mpr ⟨sub v (ff.input_mem_of_pairMember vp),
      p,q,ff.output_mem_of_pairMember vp,fg.output_mem_of_pairMember vq,vp,vq,ne⟩) va
  apply neq
  apply ext b hb c hc
  intro p _
  constructor
  · intro pb
    obtain ⟨v,va,vp⟩ := (pf a b ab p).mp pb
    obtain ⟨q,_,vq⟩ := fg.2.2 v (downE a v (fg.input_mem_of_pairMember ac) va)
    exact (pg a c ac p).mpr ⟨v,va,(same va vp vq).symm ▸ vq⟩
  · intro pc
    obtain ⟨v,va,vp⟩ := (pg a c ac p).mp pc
    obtain ⟨q,_,vq⟩ := ff.2.2 v (downD a v (ff.input_mem_of_pairMember ab) va)
    exact (pf a b ab p).mpr ⟨v,va,same va vq vp ▸ vq⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整低层解释的唯一性

低层是背景中的实际传递集，目标仍可使用任意原关系。完整前驱方程与
目标外延性逐点确定解释；只有目标确有传递隶属表示时，才还原为恒等图。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- 两张完整低层图在同一外延原关系中相同。 -/
theorem Rr_layer_d.unique_l {Γ X R H V k t : M.Domain}
    (a : Rr_layer_d I Γ X R H k) (b : Rr_layer_d I Γ X R V t) (ext : Rf_ext_d I X R) :
    H = V ∧ k = t := by
  let ρ : Env M 3 := ⟨Fin.cases k (Fin.cases t (fun _ => X)), fun _ => Γ⟩
  let φ : Delta0UnarySchema 3 := {
    body := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 4) (.imp
      (rd_entry0_m (.bound 2) (.bound 1) (.bound 3)) (.imp
        (rd_entry0_m (.bound 2) .newest (.bound 4)) (Formula.extensionalEq (.bound 1) .newest))))
    delta0 := .forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom ..)))) }
  have read x : φ.toUnarySchema.denote ρ x ↔ ∀ y, M.mem y X → ∀ z, M.mem z X →
      Rd_entry_d x y k → Rd_entry_d x z t → y = z := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1]; rfl
  have all := KP.transitive_induction_l hKP a.transitive φ ρ (by
    intro x hx ih
    apply (read x).mpr
    intro y hy z hz hxy hxz
    apply ext y hy z hz
    intro v _
    constructor
    · intro hv
      obtain ⟨s, hs, hsv⟩ := (a.predecessors x y hxy v).mp hv
      obtain ⟨w, hw, hsw⟩ := b.injection.1.2.2 s (a.transitive x hx s hs)
      have eq := (read s).mp (ih s hs) v (a.injection.1.output_mem_of_pairMember hsv) w hw hsv hsw
      exact (b.predecessors x z hxz v).mpr ⟨s, hs, eq.symm ▸ hsw⟩
    · intro hv
      obtain ⟨s, hs, hsv⟩ := (b.predecessors x z hxz v).mp hv
      obtain ⟨w, hw, hsw⟩ := a.injection.1.2.2 s (a.transitive x hx s hs)
      have eq := (read s).mp (ih s hs) w hw v (b.injection.1.output_mem_of_pairMember hsv) hsw hsv
      exact (a.predecessors x y hxy v).mpr ⟨s, hs, eq ▸ hsw⟩)
  have graph x y : Rd_entry_d x y k ↔ Rd_entry_d x y t := by
    constructor
    · intro hxy
      have hx := a.injection.1.input_mem_of_pairMember hxy
      obtain ⟨z, hz, hxz⟩ := b.injection.1.2.2 x hx
      exact ((read x).mp (all x hx) y (a.injection.1.output_mem_of_pairMember hxy) z hz hxy hxz).symm ▸ hxz
    · intro hxy
      have hx := b.injection.1.input_mem_of_pairMember hxy
      obtain ⟨z, hz, hxz⟩ := a.injection.1.2.2 x hx
      exact (read x).mp (all x hx) z hz y (b.injection.1.output_mem_of_pairMember hxy) hxz hxy ▸ hxz
  have eq := a.injection.1.1.1.eq_of_pairMember_iff hKP.1 b.injection.1.1.1 graph
  subst t
  exact ⟨ext H a.member V b.member (fun x _ => (a.image x).trans (b.image x).symm), rfl⟩

/-- 在真实传递隶属表示中，完整低层图的每个值都是原对象本身。 -/
theorem Rr_layer_d.mem_l {Γ c X R H k : M.Domain} (a : Rr_layer_d I Γ X R H k)
    (trans : M.TransitiveSet X) (model : Smem_d I c X R) :
    H = Γ ∧ ∀ x y, Rd_entry_d x y k ↔ M.mem x Γ ∧ y = x := by
  let ρ : Env M 2 := ⟨Fin.cases k (fun _ => X), fun _ => Γ⟩
  let φ : Delta0UnarySchema 2 := {
    body := Formula.forallMem (.bound 2) (.imp
      (rd_entry0_m (.bound 1) .newest (.bound 2)) (Formula.extensionalEq .newest (.bound 1)))
    delta0 := .forallMem _ (.imp (rd_entry0_delta_l ..) (.atom ..)) }
  have read x : φ.toUnarySchema.denote ρ x ↔ ∀ y, M.mem y X → Rd_entry_d x y k → y = x := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hKP.1, Formula.satisfies_extensionalEq_iff_eq hKP.1]; rfl
  have all := KP.transitive_induction_l hKP a.transitive φ ρ (by
    intro x hx ih
    apply (read x).mpr
    intro y hy hxy
    apply hKP.1.eq_of_same_members y x
    intro z
    constructor
    · intro hz
      obtain ⟨s, hs, hsz⟩ := (a.predecessors x y hxy z).mp ((model.2 z y).mpr ⟨trans y hy z hz, hy, hz⟩)
      exact ((read s).mp (ih s hs) z (a.injection.1.output_mem_of_pairMember hsz) hsz).symm ▸ hs
    · intro hz
      obtain ⟨s, hs, hzs⟩ := a.injection.1.2.2 z (a.transitive x hx z hz)
      have eq := (read z).mp (ih z hz) s hs hzs
      exact ((model.2 z y).mp ((a.predecessors x y hxy z).mpr ⟨z, hz, eq ▸ hzs⟩)).2.2)
  have graph x y : Rd_entry_d x y k ↔ M.mem x Γ ∧ y = x := by
    constructor
    · intro hxy
      have hx := a.injection.1.input_mem_of_pairMember hxy
      exact ⟨hx, (read x).mp (all x hx) y (a.injection.1.output_mem_of_pairMember hxy) hxy⟩
    · rintro ⟨hx, eq⟩
      obtain ⟨y, hy, hxy⟩ := a.injection.1.2.2 x hx
      exact eq.symm ▸ ((read x).mp (all x hx) y hy hxy ▸ hxy)
  refine ⟨hKP.1.eq_of_same_members H Γ (fun x => ⟨?_, ?_⟩), graph⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (a.image x).mp ((model.2 x H).mpr ⟨trans H a.member x hx, a.member, hx⟩)
    exact ((graph y x).mp hyx).2.symm ▸ hy
  · intro hx
    exact ((model.2 x H).mp ((a.image x).mpr ⟨x, hx, (graph x x).mpr ⟨hx, rfl⟩⟩)).2.2

end YesMetaZFC.SetTheory.Internal

/-! ## 自然数坐标与原模型的真实自然数集

完整前驱图保持零与后继。用背景 KP 的有界分离对坐标公式归纳，证明其像包含于
每个内部归纳集，故层对象就是原模型的自然数集；不要求高模型满足 KP。
原地模型的 ω 像因此与同一张实际坐标图一致。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 后继方程只读取完整前驱及两侧外延性。 -/
theorem Rr_layer_d.successor_l (hM : Extensional M) {Γ Y R w z n m : M.Domain}
    (layer : Rr_layer_d I Γ Y R w z)
    (ext : Extensional (smdl_structure_l I (R := R) ⟨w, layer.member⟩))
    (a b : (smdl_structure_l I (R := R) ⟨w, layer.member⟩).Domain)
    (hna : M.PairMember I n a.val z) (hmb : M.PairMember I m b.val z) (step : M.SuccessorOf m n) :
    (smdl_structure_l I (R := R) ⟨w, layer.member⟩).SuccessorOf b a := by
  intro x
  apply (layer.predecessors m b.val hmb x.val).trans
  constructor
  · rintro ⟨s, hs, hsx⟩
    rcases (step s).mp hs with hs | eq
    · exact Or.inl ((layer.predecessors n a.val hna x.val).mpr ⟨s, hs, hsx⟩)
    · have eq := hM.eq_of_same_members s n eq
      subst s
      have eq : x = a := Subtype.ext (layer.injection.1.1.2 n x.val a.val hsx hna)
      exact Or.inr (by rw [eq]; exact fun _ => Iff.rfl)
  · rintro (hx | eq)
    · obtain ⟨s, hs, hsx⟩ := (layer.predecessors n a.val hna x.val).mp hx
      exact ⟨s, (step s).mpr (Or.inl hs), hsx⟩
    · have eq := ext.eq_of_same_members x a eq
      subst x
      exact ⟨n, step.predecessor_mem, hna⟩

/-- 对背景全部内部自然数归纳，坐标满像在任意归纳集内。 -/
theorem Rr_layer_d.omega_l (hKP : M.Models KP) {ω Y R w z : M.Domain} (hω : M.IsOmega ω)
    (layer : Rr_layer_d I ω Y R w z)
    (ext : Extensional (smdl_structure_l I (R := R) ⟨w, layer.member⟩)) :
    (smdl_structure_l I (R := R) ⟨w, layer.member⟩).IsOmega ⟨w, layer.member⟩ := by
  let N := smdl_structure_l I (R := R) ⟨w, layer.member⟩
  have empty {e : M.Domain} (a : N.Domain) (hea : M.PairMember I e a.val z) (he : ∀ x, ¬ M.mem x e) :
      ∀ x : N.Domain, ¬ N.mem x a := fun x hx =>
    ((layer.predecessors e a.val hea x.val).mp hx).elim fun y hy => he y hy.1
  have ind : N.IsInductive ⟨w, layer.member⟩ := by
    obtain ⟨e, he, heω⟩ := hω.1.1
    obtain ⟨a, ha, hea⟩ := layer.injection.1.2.2 e heω
    refine ⟨⟨⟨a, ha⟩, empty ⟨a, ha⟩ hea he, (layer.image a).mpr ⟨e, heω, hea⟩⟩, ?_⟩
    intro a haw
    obtain ⟨n, hn, hna⟩ := (layer.image a.val).mp haw
    obtain ⟨m, step, hm⟩ := hω.1.2 n hn
    obtain ⟨b, hb, hmb⟩ := layer.injection.1.2.2 m hm
    exact ⟨⟨b, hb⟩, layer.successor_l I hKP.1 ext a ⟨b, hb⟩ hna hmb step,
      (layer.image b).mpr ⟨m, hm, hmb⟩⟩
  refine ⟨ind, fun A hA x hx => ?_⟩
  -- 坐标的值都在 Y 中；归纳性质因此只需 KP 的有界分离。
  let ρ : Env M 4 := ⟨Fin.cases z (Fin.cases R (Fin.cases A.val (fun _ => Y))), fun _ => w⟩
  let φ : Delta0UnarySchema 4 := {
    body := Formula.forallMem (.bound 4) (.imp
      (rd_entry0_m (.bound 1) .newest (.bound 2)) (rd_entry0_m .newest (.bound 4) (.bound 3)))
    delta0 := .forallMem _ (.imp (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)) }
  have entry {d} (η : Env M d) (x y r : Term d) :
      Formula.satisfies η (rd_entry0_m x y r) ↔ M.PairMember I (x.eval η) (y.eval η) (r.eval η) :=
    (rd_entry0_sat_l hKP.1 η x y r).trans ((rd_entry_sat_l hKP.1 η x y r).symm.trans
      (Formula.satisfies_orderedPairMem_iff I η x y r))
  have read n : φ.toUnarySchema.denote ρ n ↔ ∀ a, M.mem a Y → M.PairMember I n a z → M.PairMember I a A.val R := by
    simp only [φ, UnarySchema.denote,
      Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, entry]; rfl
  have all : ∀ n, M.mem n ω → φ.toUnarySchema.denote ρ n := by
    apply hω.induction (fun n => φ.toUnarySchema.denote ρ n) (KP.separation_exists_d hKP φ ρ ω)
    · intro e he
      apply (read e).mpr
      intro a _ hea
      let a₀ : N.Domain := ⟨a, layer.injection.1.output_mem_of_pairMember hea⟩
      obtain ⟨b, hb, hbA⟩ := hA.1
      have eq := ext.eq_of_same_members a₀ b (fun x => iff_of_false (empty a₀ hea he x) (hb x))
      exact show N.mem a₀ A from eq.symm ▸ hbA
    · intro n hn ih m step
      apply (read m).mpr
      intro b _ hmb
      obtain ⟨a, ha, hna⟩ := layer.injection.1.2.2 n hn
      let a₀ : N.Domain := ⟨a, ha⟩
      let b₀ : N.Domain := ⟨b, layer.injection.1.output_mem_of_pairMember hmb⟩
      obtain ⟨c, hc, hcA⟩ := hA.2 a₀ ((read n).mp ih a ha hna)
      have eq := (layer.successor_l I hKP.1 ext a₀ b₀ hna hmb step).eq ext hc
      exact show N.mem b₀ A from eq.symm ▸ hcA
  obtain ⟨n, hn, hnx⟩ := (layer.image x.val).mp hx
  exact (read n).mp (all n hn) x.val x.property hnx

/-- 实际自然数层确定原地模型 ω 的像，不把对象码等同于背景 ω。 -/
theorem Smap_d.omega_chart_l (hZF : M.Models ZF) {ω c X R d Y S q w z : M.Domain}
    (hω : M.IsOmega ω) (ht : M.TransitiveSet X) (hm : Smem_d I c X R)
    (hn : Smdl_d I d Y S) (ext : Extensional (smdl_structure_l I (R := S) hn.2.1))
    (hq : Smap_d I ω c d X Y q) (hw : M.mem ω X) (numbers : Rr_layer_d I ω Y S w z) :
    M.PairMember I ω w q := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hw⟩⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => ⟨ω, hw⟩, fun _ => ⟨ω, hw⟩⟩
  let σ : Env (smdl_structure_l I (R := R) hm.1.2.1) 1 := ⟨ρ.bound, ρ.free⟩
  let φ : Formula 1 1 := Formula.isOmega .newest
  have valid : Formula.satisfies σ φ :=
    (smem_formula_l I hm nx φ ρ).mp ((Formula.satisfies_isOmega_iff ..).mpr (rt_omega_l ht nx hZF.1 ⟨ω, hw⟩ hω))
  obtain ⟨v, hv, hwv⟩ := hq.1.1.2.2 ω hw
  let η : Env (smdl_structure_l I (R := S) hn.2.1) 1 := ⟨fun _ => ⟨v, hv⟩, fun _ => ⟨v, hv⟩⟩
  have moved := (smap_source_l I hZF hω hm.1 hn hq φ
    (by simp -implicitDefEqProofs [φ, Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed])
    σ η (fun _ => hwv)).mp valid
  have localω := (Formula.satisfies_isOmega_iff ..).mp moved
  have chartω := numbers.omega_l I (ZF.modelsKP hZF) hω ext
  have eq := ext.eq_of_same_members ⟨v, hv⟩ ⟨w, numbers.member⟩
    (fun x => ⟨localω.2 _ chartω.1 x, chartω.2 _ localω.1 x⟩)
  have same : v = w := congrArg Subtype.val eq
  exact same ▸ hwv

/-- 完整自然数坐标沿初等子模型回拉；背景内部归纳包含所有非标准长度。 -/
theorem Rr_layer_d.omega_pull_l (hZF : M.Models ZF) {Ω c X R d Y S q w v t : M.Domain}
    (hΩ : M.IsOmega Ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I Ω c d X Y q) (image : M.PairMember I w v q)
    (numbers : Rr_layer_d I Ω Y S v t) (ext : Rf_ext_d I Y S) :
    ∃ z, Rr_layer_d I Ω X R w z ∧ ∀ n x,
      M.PairMember I n x z ↔ ∃ y, M.PairMember I n y t ∧ M.PairMember I x y q := by
  let A := smdl_structure_l I (R := R) mx.2.1
  let B := smdl_structure_l I (R := S) my.2.1
  have ey := ext.native_l I my.2.1
  have hw := map.1.1.input_mem_of_pairMember image
  have hv := map.1.1.output_mem_of_pairMember image
  have natural : A.IsOmega ⟨w, hw⟩ := (Formula.satisfies_isOmega_iff ..).mp
    ((smap_source_l I hZF hΩ mx my map (n := 1) (Formula.isOmega .newest)
      (by simp -implicitDefEqProofs [Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed])
      ⟨fun _ => ⟨w, hw⟩, fun _ => ⟨w, hw⟩⟩ ⟨fun _ => ⟨v, hv⟩, fun _ => ⟨v, hv⟩⟩ (fun _ => image)).mpr
        ((Formula.satisfies_isOmega_iff ..).mpr (numbers.omega_l I (ZF.modelsKP hZF) hΩ ey)))
  let ρ : Env M 4 := ⟨Fin.cases q (Fin.cases t (Fin.cases X (fun _ => Y))), fun _ => Ω⟩
  let φ : BinarySchema 4 := { body := Formula.existsMem (.bound 5) (.conj
    (rd_entry0_m (.bound 2) .newest (.bound 4)) (rd_entry0_m (.bound 1) .newest (.bound 3))) }
  let ψ : UnarySchema 4 := { body := Formula.existsMem (.bound 3) φ.body }
  have entry {k} (η : Env M k) (a b r : Term k) :
      Formula.satisfies η (rd_entry0_m a b r) ↔ M.PairMember I (a.eval η) (b.eval η) (r.eval η) :=
    (rd_entry0_sat_l hZF.1 η a b r).trans ((rd_entry_sat_l hZF.1 η a b r).symm.trans
      (Formula.satisfies_orderedPairMem_iff I η a b r))
  have read n x : φ.denote ρ n x ↔ ∃ y, M.mem y Y ∧ M.PairMember I n y t ∧ M.PairMember I x y q := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, entry]; rfl
  have all n (hn : M.mem n Ω) : ψ.denote ρ n := by
    apply hΩ.induction (fun n => ψ.denote ρ n) (ZF.separation_exists_d hZF ψ ρ Ω) ?_ ?_ n hn
    · intro e he
      obtain ⟨e₀, he₀, heΩ⟩ := hΩ.1.1
      have eq := hZF.1.eq_of_same_members e₀ e (fun x => iff_of_false (he₀ x) (he x))
      subst e₀
      obtain ⟨b, hb, heb⟩ := numbers.injection.1.2.2 e heΩ
      obtain ⟨a, ha, _⟩ := natural.1.1
      obtain ⟨y, hy, hay⟩ := map.1.1.2.2 a.val a.property
      have empty : ∀ z : B.Domain, ¬ B.mem z ⟨y, hy⟩ := (Formula.satisfies_isEmpty_iff ..).mp
        ((smap_source_l I hZF hΩ mx my map (n := 1) (Formula.isEmpty .newest) (by simp -implicitDefEqProofs)
          ⟨fun _ => a, fun _ => a⟩ ⟨fun _ => ⟨y, hy⟩, fun _ => ⟨y, hy⟩⟩ (fun _ => hay)).mp
            ((Formula.satisfies_isEmpty_iff ..).mpr ha))
      have eq : y = b := congrArg Subtype.val (ey.eq_of_same_members ⟨y, hy⟩ ⟨b, hb⟩
        (fun x => iff_of_false (empty x) (fun h =>
          ((numbers.predecessors e b heb x.val).mp h).elim fun z hz => he z hz.1)))
      exact ⟨a.val, a.property, (read e a.val).mpr ⟨b, hb, heb, eq ▸ hay⟩⟩
    · intro n hn ih m step
      obtain ⟨x, hx, hnx⟩ := ih
      obtain ⟨y, hy, hny, hxy⟩ := (read n x).mp hnx
      have inw : A.mem ⟨x, hx⟩ ⟨w, hw⟩ :=
        (map.relation_l I hZF hΩ mx my hxy image).mpr ((numbers.image y).mpr ⟨n, hn, hny⟩)
      obtain ⟨a, ha, _⟩ := natural.1.2 ⟨x, hx⟩ inw
      obtain ⟨b, hb, hab⟩ := map.1.1.2.2 a.val a.property
      let ρ₁ : Env A 2 := ⟨Fin.cases a (fun _ => ⟨x, hx⟩), fun _ => a⟩
      let η₁ : Env B 2 := ⟨Fin.cases ⟨b, hb⟩ (fun _ => ⟨y, hy⟩), fun _ => ⟨b, hb⟩⟩
      have valid : Formula.satisfies ρ₁ (Formula.isSuccessor .newest (.bound 1)) :=
        (Formula.satisfies_isSuccessor_iff ρ₁ .newest (.bound 1)).mpr ha
      have next : B.SuccessorOf ⟨b, hb⟩ ⟨y, hy⟩ := (Formula.satisfies_isSuccessor_iff η₁ .newest (.bound 1)).mp
        ((smap_source_l I hZF hΩ mx my map (Formula.isSuccessor .newest (.bound 1))
          (by simp -implicitDefEqProofs) ρ₁ η₁ (Fin.cases hab (fun _ => hxy))).mp valid)
      obtain ⟨m₀, sm, hmΩ⟩ := hΩ.1.2 n hn
      have eq := sm.eq hZF.1 step
      subst m₀
      obtain ⟨b', hb', hmb⟩ := numbers.injection.1.2.2 m hmΩ
      have eq : b = b' := congrArg Subtype.val
        (next.eq ey (numbers.successor_l I hZF.1 ey ⟨y, hy⟩ ⟨b', hb'⟩ hny hmb step))
      exact ⟨a.val, a.property, (read m a.val).mpr ⟨b', hb', hmb, eq ▸ hab⟩⟩
  obtain ⟨z, fn, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Ω) (target := X)
    (fun n hn => (all n hn).elim fun x hx => ⟨x, hx.2⟩)
    (fun n _ x x' hx hx' => by
      obtain ⟨y, _, hny, hxy⟩ := (read n x).mp hx
      obtain ⟨y', _, hny', hx'y'⟩ := (read n x').mp hx'
      have eq := numbers.injection.1.1.2 n y y' hny hny'
      exact map.1.2 x x' y hxy (eq.symm ▸ hx'y'))
    (fun n x _ hx => (read n x).mp hx |>.elim fun _ h => map.1.1.input_mem_of_pairMember h.2.2)
  have graph n x : M.PairMember I n x z ↔ ∃ y, M.PairMember I n y t ∧ M.PairMember I x y q := by
    rw [spec]
    exact ⟨fun ⟨_, hx⟩ => (read n x).mp hx |>.elim fun y h => ⟨y, h.2⟩,
      fun ⟨y, hny, hxy⟩ => ⟨numbers.injection.1.input_mem_of_pairMember hny,
        (read n x).mpr ⟨y, numbers.injection.1.output_mem_of_pairMember hny, hny, hxy⟩⟩⟩
  refine ⟨z, ⟨numbers.transitive, hw, ⟨fn, ?_⟩, ?_, ?_⟩, graph⟩
  · intro n m x hnx hmx
    obtain ⟨y, hny, hxy⟩ := (graph n x).mp hnx
    obtain ⟨y', hmy, hxy'⟩ := (graph m x).mp hmx
    have eq := map.1.1.1.2 x y y' hxy hxy'
    exact numbers.injection.2 n m y hny (eq.symm ▸ hmy)
  · intro x
    constructor
    · intro hx
      obtain ⟨y, _, hxy⟩ := map.1.1.2.2 x (mx.2.2.2 x w hx).1
      obtain ⟨n, hn, hny⟩ := (numbers.image y).mp ((map.relation_l I hZF hΩ mx my hxy image).mp hx)
      exact ⟨n, hn, (graph n x).mpr ⟨y, hny, hxy⟩⟩
    · rintro ⟨n, hn, hnx⟩
      obtain ⟨y, hny, hxy⟩ := (graph n x).mp hnx
      exact (map.relation_l I hZF hΩ mx my hxy image).mpr ((numbers.image y).mpr ⟨n, hn, hny⟩)
  · intro n x hnx a
    obtain ⟨y, hny, hxy⟩ := (graph n x).mp hnx
    constructor
    · intro ha
      obtain ⟨b, _, hab⟩ := map.1.1.2.2 a (mx.2.2.2 a x ha).1
      obtain ⟨m, hm, hmb⟩ := (numbers.predecessors n y hny b).mp
        ((map.relation_l I hZF hΩ mx my hab hxy).mp ha)
      exact ⟨m, hm, (graph m a).mpr ⟨b, hmb, hab⟩⟩
    · rintro ⟨m, hm, hma⟩
      obtain ⟨b, hmb, hab⟩ := (graph m a).mp hma
      exact (map.relation_l I hZF hΩ mx my hab hxy).mpr
        ((numbers.predecessors n y hny b).mpr ⟨m, hm, hmb⟩)

/-- 只有在实际传递隶属模型中，完整数字坐标才逐点还原为背景恒等图。 -/
theorem Rr_layer_d.omega_mem_l (hKP : M.Models KP) {Ω c X R w z : M.Domain}
    (hΩ : M.IsOmega Ω) (layer : Rr_layer_d I Ω X R w z)
    (trans : M.TransitiveSet X) (model : Smem_d I c X R) :
    w = Ω ∧ ∀ n x, M.PairMember I n x z ↔ M.mem n Ω ∧ x = n := by
  let N := smdl_structure_l I (R := R) model.1.2.1
  have ext := smem_ext_l I model.1 model.2 trans hKP.1
  let ρ : Env M 2 := ⟨Fin.cases z (fun _ => X), fun _ => Ω⟩
  let φ : Delta0UnarySchema 2 := {
    body := Formula.forallMem (.bound 2) (.imp
      (rd_entry0_m (.bound 1) .newest (.bound 2)) (Formula.extensionalEq .newest (.bound 1)))
    delta0 := .forallMem _ (.imp (rd_entry0_delta_l ..) (.atom ..)) }
  have entry {d} (η : Env M d) (a b f : Term d) :
      Formula.satisfies η (rd_entry0_m a b f) ↔ M.PairMember I (a.eval η) (b.eval η) (f.eval η) :=
    (rd_entry0_sat_l hKP.1 η a b f).trans ((rd_entry_sat_l hKP.1 η a b f).symm.trans
      (Formula.satisfies_orderedPairMem_iff I η a b f))
  have read n : φ.toUnarySchema.denote ρ n ↔ ∀ x, M.mem x X → M.PairMember I n x z → x = n := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      entry, Formula.satisfies_extensionalEq_iff_eq hKP.1]; rfl
  have all : ∀ n, M.mem n Ω → φ.toUnarySchema.denote ρ n := by
    apply hΩ.induction (fun n => φ.toUnarySchema.denote ρ n) (KP.separation_exists_d hKP φ ρ Ω)
    · intro e he
      apply (read e).mpr
      intro a ha hea
      exact hKP.1.eq_of_same_members a e (fun x => iff_of_false
        (fun hx => ((layer.predecessors e a hea x).mp
          ((model.2 x a).mpr ⟨trans a ha x hx, ha, hx⟩)).elim fun y hy => he y hy.1) (he x))
    · intro n hn ih m step
      apply (read m).mpr
      intro a ha hma
      obtain ⟨b, hb, hnb⟩ := layer.injection.1.2.2 n hn
      have eq := (read n).mp ih b hb hnb
      subst b
      have next := layer.successor_l I hKP.1 ext (⟨n, hb⟩ : N.Domain) ⟨a, ha⟩ hnb hma step
      let η : Env N 2 := ⟨Fin.cases ⟨a, ha⟩ (fun _ => ⟨n, hb⟩), fun _ => ⟨n, hb⟩⟩
      have valid := (KP.succ0_sat_l ext η .newest (.bound 1)).mpr next
      have absolute := (smem_delta_image_l I model trans (KP.succ0_delta_l ..) η).mp valid
      have actual : M.SuccessorOf a n := (KP.succ0_sat_l hKP.1 ..).mp absolute
      exact actual.eq hKP.1 step
  have graph n x : M.PairMember I n x z ↔ M.mem n Ω ∧ x = n := by
    constructor
    · intro hnx
      have hn := layer.injection.1.input_mem_of_pairMember hnx
      exact ⟨hn, (read n).mp (all n hn) x (layer.injection.1.output_mem_of_pairMember hnx) hnx⟩
    · rintro ⟨hn, eq⟩
      subst x
      obtain ⟨a, ha, hna⟩ := layer.injection.1.2.2 n hn
      exact (read n).mp (all n hn) a ha hna ▸ hna
  refine ⟨hKP.1.eq_of_same_members w Ω (fun x => ⟨?_, ?_⟩), graph⟩
  · intro hx
    obtain ⟨n, hn, hnx⟩ := (layer.image x).mp ((model.2 x w).mpr ⟨trans w layer.member x hx, layer.member, hx⟩)
    exact ((graph n x).mp hnx).2.symm ▸ hn
  · intro hx
    exact ((model.2 x w).mp ((layer.image x).mpr ⟨x, hx, (graph x x).mpr ⟨hx, rfl⟩⟩)).2.2

/-- 两张完整自然数坐标图逐点相同；闭包证书可使用实际递归给出的任一张图。 -/
theorem Rr_layer_d.omega_unique_l (hKP : M.Models KP) {ω X R w v z t : M.Domain}
    (hω : M.IsOmega ω) (a : Rr_layer_d I ω X R w z) (b : Rr_layer_d I ω X R v t)
    (ext : Rf_ext_d I X R) : w = v ∧ z = t := by
  let N := smdl_structure_l I (R := R) ⟨w, a.member⟩
  have en := ext.native_l I ⟨w, a.member⟩
  let ρ : Env M 3 := ⟨Fin.cases z (Fin.cases t (fun _ => X)), fun _ => ω⟩
  let φ : Delta0UnarySchema 3 := {
    body := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 4) (.imp
      (rd_entry0_m (.bound 2) (.bound 1) (.bound 3)) (.imp
        (rd_entry0_m (.bound 2) .newest (.bound 4)) (Formula.extensionalEq (.bound 1) .newest))))
    delta0 := .forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom ..)))) }
  have entry {d} (η : Env M d) (x y r : Term d) :
      Formula.satisfies η (rd_entry0_m x y r) ↔ M.PairMember I (x.eval η) (y.eval η) (r.eval η) :=
    (rd_entry0_sat_l hKP.1 η x y r).trans ((rd_entry_sat_l hKP.1 η x y r).symm.trans
      (Formula.satisfies_orderedPairMem_iff I η x y r))
  have read n : φ.toUnarySchema.denote ρ n ↔ ∀ x, M.mem x X → ∀ y, M.mem y X →
      M.PairMember I n x z → M.PairMember I n y t → x = y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      entry, Formula.satisfies_extensionalEq_iff_eq hKP.1]; rfl
  have all : ∀ n, M.mem n ω → φ.toUnarySchema.denote ρ n := by
    apply hω.induction (fun n => φ.toUnarySchema.denote ρ n) (KP.separation_exists_d hKP φ ρ ω)
    · intro e he
      apply (read e).mpr
      intro x hx y hy hex hey
      apply ext x hx y hy
      intro u _
      exact iff_of_false (fun h => ((a.predecessors e x hex u).mp h).elim fun n hn => he n hn.1)
        (fun h => ((b.predecessors e y hey u).mp h).elim fun n hn => he n hn.1)
    · intro n hn ih m step
      apply (read m).mpr
      intro x hx y hy hmx hmy
      obtain ⟨p, hp, hnp⟩ := a.injection.1.2.2 n hn
      obtain ⟨q, hq, hnq⟩ := b.injection.1.2.2 n hn
      have eq := (read n).mp ih p hp q hq hnp hnq
      subst q
      have left := a.successor_l I hKP.1 en (⟨p, hp⟩ : N.Domain) ⟨x, hx⟩ hnp hmx step
      have right := b.successor_l I hKP.1 en (⟨p, hp⟩ : N.Domain) ⟨y, hy⟩ hnq hmy step
      exact congrArg Subtype.val (left.eq en right)
  have graph n x : M.PairMember I n x z ↔ M.PairMember I n x t := by
    constructor
    · intro hnx
      have hn := a.injection.1.input_mem_of_pairMember hnx
      obtain ⟨y, hy, hny⟩ := b.injection.1.2.2 n hn
      exact ((read n).mp (all n hn) x (a.injection.1.output_mem_of_pairMember hnx) y hy hnx hny).symm ▸ hny
    · intro hnx
      have hn := b.injection.1.input_mem_of_pairMember hnx
      obtain ⟨y, hy, hny⟩ := a.injection.1.2.2 n hn
      exact (read n).mp (all n hn) y hy x (b.injection.1.output_mem_of_pairMember hnx) hny hnx ▸ hny
  have eq := a.injection.1.1.1.eq_of_pairMember_iff hKP.1 b.injection.1.1.1 graph
  subst t
  exact ⟨ext w a.member v b.member (fun x _ => (a.image x).trans (b.image x).symm), rfl⟩

/-- 初等图保持原生 ω；两张完整数字坐标因此逐点交换。 -/
theorem Rr_layer_d.omega_map_l (hZF : M.Models ZF) {ω c X R d Y S q w v z t : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y q) (ext : Rf_ext_d I X R) (ext' : Rf_ext_d I Y S)
    (source : Rr_layer_d I ω X R w z) (target : Rr_layer_d I ω Y S v t) :
    M.PairMember I w v q ∧
      ∀ n x y, M.PairMember I n x z → M.PairMember I n y t → M.PairMember I x y q := by
  let A := smdl_structure_l I (R := R) mx.2.1
  let B := smdl_structure_l I (R := S) my.2.1
  have ey := ext'.native_l I my.2.1
  obtain ⟨v₀, hv₀, image⟩ := map.1.1.2.2 w source.member
  let ρ : Env A 1 := ⟨fun _ => ⟨w, source.member⟩, fun _ => ⟨w, source.member⟩⟩
  let η : Env B 1 := ⟨fun _ => ⟨v₀, hv₀⟩, fun _ => ⟨v₀, hv₀⟩⟩
  have natural : B.IsOmega ⟨v₀, hv₀⟩ := (Formula.satisfies_isOmega_iff η .newest).mp
    ((smap_source_l I hZF hω mx my map (Formula.isOmega .newest)
      (by simp -implicitDefEqProofs [Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed])
      ρ η (fun _ => image)).mp ((Formula.satisfies_isOmega_iff ρ .newest).mpr
        (source.omega_l I (ZF.modelsKP hZF) hω (ext.native_l I mx.2.1))))
  have native := target.omega_l I (ZF.modelsKP hZF) hω ey
  have eq : v₀ = v := congrArg Subtype.val (ey.eq_of_same_members ⟨v₀, hv₀⟩ ⟨v, target.member⟩
    (fun x => ⟨natural.2 _ native.1 x, native.2 _ natural.1 x⟩))
  have hw : M.PairMember I w v q := eq ▸ image
  obtain ⟨s, pulled, graph⟩ := target.omega_pull_l I hZF hω mx my map hw ext'
  have eq := (source.omega_unique_l I (ZF.modelsKP hZF) hω pulled ext).2
  subst s
  refine ⟨hw, fun n x y hnx hny => ?_⟩
  obtain ⟨y', hny', hxy⟩ := (graph n x).mp hnx
  exact target.injection.1.1.2 n y' y hny' hny ▸ hxy

/-- 完整数字坐标在实际传递隶属像中逐点还原为背景自然数。 -/
theorem Rr_layer_d.omega_image_mem_l (hZF : M.Models ZF) {Ω c X R d Y S q w z : M.Domain}
    (hΩ : M.IsOmega Ω) (numbers : Rr_layer_d I Ω X R w z) (ext : Rf_ext_d I X R)
    (mx : Smdl_d I c X R) (my : Smem_d I d Y S) (trans : M.TransitiveSet Y)
    (map : Smap_d I Ω c d X Y q) : M.PairMember I w Ω q ∧
      ∀ n x, M.PairMember I n x z → M.PairMember I x n q := by
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 1 :=
    ⟨fun _ => ⟨w, numbers.member⟩, fun _ => ⟨w, numbers.member⟩⟩
  have native : Rr_truth_d I X R (Formula.isOmega .newest) (fun _ : Fin 1 => w) :=
    (rr_truth_native_l I mx.2.1 (Formula.isOmega .newest)
      (by simp -implicitDefEqProofs [Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed])
      (fun _ => ⟨w, numbers.member⟩)).mpr ((Formula.satisfies_isOmega_iff ρ .newest).mpr
        (numbers.omega_l I (ZF.modelsKP hZF) hΩ (ext.native_l I mx.2.1)))
  obtain ⟨v, hv, image⟩ := map.1.1.2.2 w numbers.member
  have ordinal := (numbers.ordinal_l I hZF.1 (hΩ.isOrdinal (ZF.modelsKP hZF))).map_l I hZF hΩ
    mx my.1 map (by simp -implicitDefEqProofs) (fun _ => image)
  have ov : M.IsOrdinal v := (KP.ord0_sat_l (ZF.modelsKP hZF) (⟨fun _ => v, fun _ => v⟩ : Env M 1) .newest).mp
    ((rr_truth_mem_l I trans my (KP.ord0_m .newest) (KP.ord0_delta_l ..) (fun _ => v)).mp ordinal).2
  have natural := native.map_l I hZF hΩ mx my.1 map
    (by simp -implicitDefEqProofs [Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed]) (fun _ => image)
  let ny : Nonempty {y // M.mem y Y} := ⟨⟨v, hv⟩⟩
  let η : Env (rt_model_l Y ny) 1 := ⟨fun _ => ⟨v, hv⟩, fun _ => ⟨v, hv⟩⟩
  have nv : (rt_model_l Y ny).IsOmega ⟨v, hv⟩ := (Formula.satisfies_isOmega_iff η .newest).mp
    ((smem_formula_l I my ny (Formula.isOmega .newest) η).mpr
      ((rr_truth_native_l I my.1.2.1 _
        (by simp -implicitDefEqProofs [Formula.isOmega, Formula.isInductive, Definitional.Formula.FreeClosed])
        (fun _ => ⟨v, hv⟩)).mp natural))
  have sub := hΩ.2 v ((rt_inductive_l trans ny hZF.1 ⟨v, hv⟩).mp nv.1)
  have eq : v = Ω := by
    rcases ov.trichotomy hZF.1 (hΩ.isOrdinal (ZF.modelsKP hZF))
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) v Ω) with eq | lt | gt
    · exact hZF.1.eq_of_same_members v Ω eq
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) v (sub v lt)).elim
    · have hw := trans v hv Ω gt
      have nw := rt_omega_l trans ny hZF.1 ⟨Ω, hw⟩ hΩ
      exact congrArg Subtype.val ((rt_model_ext_l hZF.1 trans ny).eq_of_same_members ⟨v, hv⟩ ⟨Ω, hw⟩
        (fun x => ⟨nv.2 _ nw.1 x, nw.2 _ nv.1 x⟩))
  subst v
  obtain ⟨t, target, identity⟩ := rr_layer_mem_l I hZF my trans hv (hΩ.transitive (ZF.modelsKP hZF))
  obtain ⟨s, source, graph⟩ := target.omega_pull_l I hZF hΩ mx my.1 map image (rf_ext_mem_l I hZF.1 trans my)
  have eq := (numbers.omega_unique_l I (ZF.modelsKP hZF) hΩ source ext).2
  subst s
  refine ⟨image, fun n x hnx => ?_⟩
  obtain ⟨y, hny, hxy⟩ := (graph n x).mp hnx
  exact ((identity n y).mp hny).2.symm ▸ hxy

end YesMetaZFC.SetTheory.Internal

/-! ## 完整数字图保持全部内部轮次的奇偶

对背景模型的整个自然数集作可定义归纳。数字图将零和后继同步到原关系，
两侧已证的奇偶翻转因此逐步相同；不把非标准自然数当作外部有限数处理。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Rr_layer_d.even_l {Ω X R w z m : M.Domain}
    (layer : Rr_layer_d I Ω X R w z) (hΩ : M.IsOmega Ω)
    (hN : (smdl_structure_l I (R := R) ⟨w,layer.member⟩).Models ZF)
    (hm : M.mem m Ω) (n : (smdl_structure_l I (R := R) ⟨w,layer.member⟩).Domain)
    (point : M.PairMember I m n.val z) :
    Gm_even_d I Ω m ↔ Gm_even_d (kp_pair_l (ZF.modelsKP hN)) ⟨w,layer.member⟩ n := by
  let N := smdl_structure_l I (R := R) ⟨w,layer.member⟩
  let J := kp_pair_l (ZF.modelsKP hN)
  let ψ : Formula 1 2 := gm_even_m (𝒞 := kpair_convention_l) (.bound 0) (.bound 1)
  have closed : ψ.FreeClosed := by simp -implicitDefEqProofs [ψ]
  let ρ : Env M 5 := ⟨fun i => [Ω,X,R,w,z].get i,fun _ => w⟩
  let φ : UnarySchema 5 := {
    body := Formula.forallMem (.bound 2)
      (.imp (rd_entry0_m (.bound 1) .newest (.bound 6))
        (.iff (gm_even_m (𝒞 := kpair_convention_l) (.bound 2) (.bound 1))
          (rr_truth_m (𝒞 := kpair_convention_l) ψ (.bound 3) (.bound 4)
            (Fin.cases (.bound 5) (fun _ => .newest)))))
    freeClosed := by
      simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
      exact rr_truth_closed_l ψ closed _ _ _ rfl rfl (Fin.cases rfl (fun _ => rfl)) }
  have read (k : M.Domain) : φ.denote ρ k ↔ ∀ a, M.mem a X → M.PairMember I k a z →
      (Gm_even_d I Ω k ↔ Rr_truth_d I X R ψ (Fin.cases w (fun _ => a))) := by
    have row {d} (ζ : Env M d) (a b : Term d) :
        (fun i : Fin 2 => ((Fin.cases a (fun _ => b) : Fin 2 → Term d) i).eval ζ) =
          Fin.cases (a.eval ζ) (fun _ => b.eval ζ) := funext (Fin.cases rfl (fun _ => rfl))
    simp only [φ,UnarySchema.denote,Formula.satisfies_forallMem_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,Formula.satisfies_iff_iff,gm_even_sat_l I hZF.1,
      rr_truth_sat_l I _ ψ closed,row]
    rfl
  have native (a : N.Domain) : Rr_truth_d I X R ψ (Fin.cases w (fun _ => a.val)) ↔
      Gm_even_d J ⟨w,layer.member⟩ a := by
    have row : (fun i : Fin 2 => ((Fin.cases ⟨w,layer.member⟩ (fun _ => a) : Fin 2 → N.Domain) i).val) =
        Fin.cases w (fun _ => a.val) := funext (Fin.cases rfl (fun _ => rfl))
    rw [← row]
    exact (rr_truth_native_l I ⟨w,layer.member⟩ ψ closed
      (Fin.cases ⟨w,layer.member⟩ (fun _ => a))).trans
      (gm_even_sat_l J hN.1 (⟨Fin.cases ⟨w,layer.member⟩ (fun _ => a),fun _ => ⟨w,layer.member⟩⟩ :
        Env N 2) (.bound 0) (.bound 1))
  have omegaN := layer.omega_l I (ZF.modelsKP hZF) hΩ hN.1
  have all : ∀ k, M.mem k Ω → φ.denote ρ k := by
    apply hΩ.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ Ω)
    · intro e he
      apply (read e).mpr
      intro a ha hea
      have zero : ∀ b : N.Domain, ¬ N.mem b ⟨a,ha⟩ := fun b hb =>
        ((layer.predecessors e a hea b.val).mp hb).elim fun c hc => he c hc.1
      exact iff_of_true (gm_even_zero_l I hZF hΩ he)
        ((native ⟨a,ha⟩).mpr (gm_even_zero_l J hN omegaN zero))
    · intro k hk ih l succ
      apply (read l).mpr
      intro b hb hlb
      obtain ⟨a,ha,hka⟩ := layer.injection.1.2.2 k hk
      have step := layer.successor_l I hZF.1 hN.1 ⟨a,ha⟩ ⟨b,hb⟩ hka hlb succ
      have prior := ((read k).mp ih a ha hka).trans (native ⟨a,ha⟩)
      have member : N.mem ⟨a,ha⟩ ⟨w,layer.member⟩ := (layer.image a).mpr ⟨k,hk,hka⟩
      exact (gm_even_successor_l I hZF hΩ hk succ).trans ((not_congr prior).trans
        ((gm_even_successor_l J hN omegaN member step).symm.trans (native ⟨b,hb⟩).symm))
  exact ((read m).mp (all m hm) n.val n.property point).trans (native n)

end YesMetaZFC.SetTheory.Internal
