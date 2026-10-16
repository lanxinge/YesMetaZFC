import YesMetaZFC.Model.Forcing.Internal.Embedding.Rank
import YesMetaZFC.Model.Forcing.Applications.Collapse.FiniteSequence
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # 7.22 的小坍缩提升在实际迭代秩段上的实例

源中的全部内部有限 κ 列作为有界关系族进入共同的低极限秩段。
因此无需另交条件覆盖、稠密集覆盖或目标泛型性；它们都由原秩证书恢复。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smem_d.fseq_rank_l {c X R μ V : M.Domain} (xt : M.TransitiveSet X)
    (mx : Smem_d I c X R) (hV : M.mem V X) (rank : Vr_d X μ V) (limit : M.IsLimitOrdinal μ)
    (hA : (smdl_structure_l I (R := R) mx.1.2.1).Models ZF)
    (ω κ P : (smdl_structure_l I (R := R) mx.1.2.1).Domain) (hw : M.IsOmega ω.val)
    (hωV : M.mem ω.val V) (hκV : M.mem κ.val V)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hA)) ω κ P) : M.mem P.val V := by
  let A := smdl_structure_l I (R := R) mx.1.2.1
  apply rank.relations_mem_l xt hV limit hωV hκV P.property
  intro f hf p hp
  let f' : A.Domain := ⟨f, xt P.val P.property f hf⟩
  obtain ⟨n, hn, fn⟩ := (space f').mp ((mx.2 f P.val).mpr ⟨f'.property, P.property, hf⟩)
  let ρ : Env A 3 := ⟨Fin.cases f' (Fin.cases κ (fun _ => n)), fun _ => n⟩
  have fn' : Fn0_d n.val κ.val f :=
    (fn0_sat_l hZF.1 (@image_env_l A M Subtype.val 3 ρ) (.bound 2) (.bound 1) .newest).mp
      ((smem_delta_image_l I mx xt (fn0_delta_l ..) ρ).mp
        ((fn0_sat_l hA.1 ρ (.bound 2) (.bound 1) .newest).mpr (fn0_of_function_l (ZF.modelsKP hA) fn)))
  obtain ⟨i, hi, a, ha, pair⟩ := fn'.1 p hp
  exact ⟨i, hw.transitive hZF n.val ((mx.2 n.val ω.val).mp hn).2.2 i hi, a, ha, pair⟩

/-- 原内部有限条件及给定小泛型，自动提升已有初等图并保持同一个滤子。 -/
theorem Smap_d.collapse_lift_l {ω c d X R Y S j μ ν V : M.Domain}
    (hw : M.IsOmega ω) (xt : M.TransitiveSet X) (yt : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (map : Smap_d I ω c d X Y j)
    (hμ : Rd_entry_d μ ν j) (fixed : ∀ β, M.mem β μ → Rd_entry_d β β j)
    (hVX : M.mem V X) (rx : Vr_d X μ V) (hVY : M.mem V Y) (ry : Vr_d Y μ V)
    (limit : M.IsLimitOrdinal μ) (hωμ : M.mem ω μ)
    (hA : (smdl_structure_l I (R := R) mx.1.2.1).Models ZF)
    (hB : (smdl_structure_l I (R := S) my.1.2.1).Models ZF)
    (w κ P Q : (smdl_structure_l I (R := R) mx.1.2.1).Domain) (hw' : w.val = ω) (hκμ : M.mem κ.val μ)
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hA)) w κ P)
    (O : Cond_order_d _ P Q P) {U} (generic : Generic_d _ P Q P U) :
    ∃ e : (smdl_structure_l I (R := R) mx.1.2.1).Domain → (smdl_structure_l I (R := S) my.1.2.1).Domain,
      Pe_d e ∧ (∀ x, Rd_entry_d x.val (e x).val j) ∧
      Generic_d _ (e P) (e Q) (e P) (Em_generic_d e U) ∧
      (∀ q, Em_generic_d e U q ↔ ∃ p, U p ∧ p.val = q.val) ∧
      ∃ f : (extension_l _ hA P Q P U).Domain → (extension_l _ hB (e P) (e Q) (e P) (Em_generic_d e U)).Domain,
        Function.Injective f ∧
        (∀ t x, Qval_d _ P Q P U t x → Qval_d _ (e P) (e Q) (e P) (Em_generic_d e U) (e t) (f x)) ∧
        ∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ ρ, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l f ρ) φ := by
  have low := rx.ordinal_subset_l hZF xt hVX
  have hp := mx.fseq_rank_l hZF xt hVX rx limit hA w κ P (hw'.symm ▸ hw)
    (hw'.symm ▸ low ω hωμ) (low κ.val hκμ) space
  exact map.rank_lift_l hZF hw xt yt mx my hμ fixed hVX rx hVY ry hA hB P Q P hp O generic

end YesMetaZFC.SetTheory.Internal
