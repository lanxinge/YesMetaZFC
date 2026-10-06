import YesMetaZFC.Model.SetTheory.Internal.SourceHierarchy
import YesMetaZFC.SetTheory.Hereditary

/-! # 源内传递包络

每个源内集合的成员同时落在一个源内传递集合中。秩层直接取较早层，
初等传输覆盖全部新参数；相对秩段直接读取原历史，无需增加正则性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_cover_d (X : M.Domain) : Prop := ∀ A, M.mem A X →
  ∃ T, M.mem T X ∧ M.TransitiveSet T ∧ M.MemberSubset A T

def sc_cover_m : Formula 1 0 := .forallE (.existsE
  (.conj (Formula.isTransitive .newest) (Formula.subset (.bound 1) .newest)))
derive_free_closed sc_cover_m

theorem sc_cover_sat_l {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x // M.mem x X}) (ρ : Env (rt_model_l X hn) 0) :
    Formula.satisfies ρ sc_cover_m ↔ Sc_cover_d X := by
  have matrix (η : Env (rt_model_l X hn) 2) : Formula.satisfies η
      (.conj (Formula.isTransitive .newest) (Formula.subset (.bound 1) .newest)) ↔
      M.TransitiveSet (η.bound 0).val ∧ M.MemberSubset (η.bound 1).val (η.bound 0).val :=
    (rt_model_delta_l hX hn (.conj (.forallMem _ (.forallMem _ (.mem ..))) (.atom ..)) η).trans
      ((Formula.satisfies_conj_iff ..).trans (and_congr (Formula.satisfies_isTransitive_iff ..) (Formula.satisfies_subset_iff ..)))
  simp only [sc_cover_m, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, matrix]
  exact ⟨fun h A hA => (h ⟨A, hA⟩).elim fun T ht => ⟨T.val, T.property, ht⟩,
    fun h A => (h A.val A.property).elim fun T ht => ⟨⟨T, ht.1⟩, ht.2⟩⟩

theorem sc_v_cover_l (hZF : M.Models ZF) {δ X : M.Domain}
    (hx : V_d (kp_pair_l (ZF.modelsKP hZF)) δ X) : Sc_cover_d X := by
  intro A hA
  obtain ⟨β, T, hβ, ht, sub⟩ := (ZF.v_unfold_l _ hZF hx A).mp hA
  exact ⟨T, ZF.v_mem_l _ hZF ht hx hβ, ZF.v_transitive_l _ hZF ht, sub⟩

theorem sc_h_cover_l (hZF : M.Models ZF) {χ X : M.Domain} (hχ : M.IsLimitOrdinal χ)
    (hx : H_d (kp_pair_l (ZF.modelsKP hZF)) χ X) : Sc_cover_d X := by
  intro A hA
  obtain ⟨T, μ, ht, hμ, size⟩ := (hx A).mp hA
  exact ⟨T, (hx T).mpr (ZF.hmem_of_subset_l _ hZF hχ ht.1 (fun _ h => h) hμ size), ht.1, ht.1 A ht.2.1⟩

theorem sc_cover_iff_l (hZF : M.Models ZF) {ω c d X R Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) : Sc_cover_d X ↔ Sc_cover_d Y := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  obtain ⟨y, hy⟩ := hn.1.2.1
  let nx : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨y, hy⟩⟩
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  let η : Env (rt_model_l Y ny) 0 := ⟨Fin.elim0, fun _ => ⟨y, hy⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ he, hn.empty_pred_l _ he, hj⟩ nx ny
    sc_cover_m (by simp -implicitDefEqProofs [sc_cover_m, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)
  exact (sc_cover_sat_l hX nx ρ).symm.trans (tr.trans (sc_cover_sat_l hY ny η))

theorem sc_rank_cover_l (hZF : M.Models ZF) {Z α V : M.Domain}
    (hZ : M.TransitiveSet Z) (hV : M.mem V Z) (rank : Vr_d Z α V) : Sc_cover_d V := by
  obtain ⟨B, F, hB, _, cert⟩ := rank
  intro A hA
  obtain ⟨β, hβ, T, hT, hβT, sub⟩ := ((cert A (hZ V hV A hA)).2.2.2).mp hA
  exact ⟨T, ((cert T (hZ B hB T hT)).2.2.2).mpr ⟨β, hβ, T, hT, hβT, fun _ h => h⟩,
    (vc_transitive_l hZF hZ hV hB cert).2 β hβ T hβT, sub⟩

end YesMetaZFC.SetTheory.Internal
