import YesMetaZFC.Model.Forcing.Internal.Embedding.Generic
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingProject
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRankFixed
import YesMetaZFC.SetTheory.CumulativeRelativeClosure

/-! # 共同低秩段上的实际小力迫提升

迭代已有的共同相对秩段和临界点以下固定性，自动给出条件及所有目标
稠密集的旧原像。随后实际证明目标泛型性并构造 [τ]↦[j(τ)] 的初等提升。
这里保留源内幂集，不把它替换为背景幂集。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

namespace Internal
open YesMetaZFC.Model.Forcing.Internal

theorem Smap_d.rank_lift_l {ω c d X R Y S j κ ℓ V : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y j)
    (hκ : Rd_entry_d κ ℓ j) (fixed : ∀ β, M.mem β κ → Rd_entry_d β β j)
    (hVX : M.mem V X) (rx : Vr_d X κ V) (hVY : M.mem V Y) (ry : Vr_d Y κ V)
    (hA : (smdl_structure_l I (R := R) mx.1.2.1).Models ZF)
    (hB : (smdl_structure_l I (R := S) my.1.2.1).Models ZF)
    (P Q z : (smdl_structure_l I (R := R) mx.1.2.1).Domain) (hp : M.mem P.val V)
    (O : Cond_order_d _ P Q z) {U} (generic : Generic_d _ P Q z U) :
    ∃ e : (smdl_structure_l I (R := R) mx.1.2.1).Domain → (smdl_structure_l I (R := S) my.1.2.1).Domain,
      Pe_d e ∧ (∀ x, Rd_entry_d x.val (e x).val j) ∧
      Generic_d _ (e P) (e Q) (e z) (Em_generic_d e U) ∧
      (∀ q, Em_generic_d e U q ↔ ∃ p, U p ∧ p.val = q.val) ∧
      ∃ f : (extension_l _ hA P Q z U).Domain → (extension_l _ hB (e P) (e Q) (e z) (Em_generic_d e U)).Domain,
        Function.Injective f ∧
        (∀ t x, Qval_d _ P Q z U t x → Qval_d _ (e P) (e Q) (e z) (Em_generic_d e U) (e t) (f x)) ∧
        ∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ ρ, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l f ρ) φ := by
  let A := smdl_structure_l I (R := R) mx.1.2.1
  let B := smdl_structure_l I (R := S) my.1.2.1
  obtain ⟨e, elem, values⟩ := map.project_l I hZF hw mx.1 my.1
  have low := map.rank_fixed_l hZF hw xt yt mx my hκ fixed hVX rx hVY ry
  have vt := rx.transitive_l hZF xt hVX
  have value (a : A.Domain) (ha : M.mem a.val V) : (e a).val = a.val :=
    map.1.1.1.2 a.val (e a).val a.val (values a) (low a.val ha)
  have eP := value P hp
  have conditions (q : B.Domain) (hq : B.mem q (e P)) : ∃ p : A.Domain, A.mem p P ∧ e p = q := by
    have qP : M.mem q.val P.val := eP ▸ ((my.2 q.val (e P).val).mp hq).2.2
    let p : A.Domain := ⟨q.val, xt V hVX q.val (vt P.val hp q.val qP)⟩
    exact ⟨p, (mx.2 p.val P.val).mpr ⟨p.property, P.property, qP⟩,
      Subtype.ext (value p (vt P.val hp q.val qP))⟩
  have subsets (D : B.Domain) (sub : B.MemberSubset D (e P)) : ∃ C : A.Domain, e C = D := by
    have bound : M.MemberSubset D.val P.val := by
      intro q hq
      let q' : B.Domain := ⟨q, yt D.val D.property q hq⟩
      exact eP ▸ ((my.2 q (e P).val).mp (sub q' ((my.2 q D.val).mpr ⟨q'.property, D.property, hq⟩))).2.2
    have hd := ry.subset_mem_l yt hVY hp D.property bound
    let C : A.Domain := ⟨D.val, xt V hVX D.val hd⟩
    exact ⟨C, Subtype.ext (value C hd)⟩
  obtain ⟨hG, f, injective, names, elementary⟩ := em_small_lift_l hA hB e elem O generic conditions subsets
  refine ⟨e, elem, values, hG, ?_, f, injective, names, elementary⟩
  intro q
  constructor
  · rintro ⟨p, hpU, rfl⟩
    have pP := ((mx.2 p.val P.val).mp (generic.proper p hpU).1).2.2
    exact ⟨p, hpU, (value p (vt P.val hp p.val pP)).symm⟩
  · rintro ⟨p, hpU, eq⟩
    have pP := ((mx.2 p.val P.val).mp (generic.proper p hpU).1).2.2
    exact ⟨p, hpU, Subtype.ext ((value p (vt P.val hp p.val pP)).trans eq)⟩

end Internal
end YesMetaZFC.SetTheory
