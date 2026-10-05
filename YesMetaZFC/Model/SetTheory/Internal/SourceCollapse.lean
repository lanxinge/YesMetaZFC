import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOmega
import YesMetaZFC.SetTheory.HereditaryCollapse

/-! # 塌缩存在句子的源模型闭包与初等保持

良基性只检查当前模型中的子集。Hχ 含载体的全部实际子集，故其相对良基性
给出背景良基性，再由实际关系递归构造塌缩。整条存在句子沿初等嵌入传递，
因此覆盖目标模型中新出现的关系，而不限于旧嵌入的像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_wf_d (X A R : M.Domain) : Prop :=
  ∀ Y, M.mem Y X → M.MemberSubset Y A → (∃ a, M.mem a Y) →
    ∃ a, M.mem a Y ∧ ∀ b, M.mem b Y → ¬ Rd_entry_d b a R

def Sc_collapse_d (X : M.Domain) : Prop :=
  ∀ A R, M.mem A X → M.mem R X → Sc_wf_d X A R →
    ∃ B F, M.mem B X ∧ M.mem F X ∧ Wc_map_d A R B F

def sc_collapse_m : Formula 1 0 := .forallE (.forallE
  (.imp (wf_rel_m (.bound 1) .newest)
    (.existsE (.existsE (wc_map_m (.bound 3) (.bound 2) (.bound 1) .newest)))))

theorem sc_wf_relative_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x : M.Domain // M.mem x X}) (A R : (rt_model_l X hn).Domain) :
    Wf_rel_d A R ↔ Sc_wf_d X A.val R.val := by
  let N := rt_model_l X hn
  have en (a b : N.Domain) : Rd_entry_d a b R ↔ Rd_entry_d a.val b.val R.val := by
    let ρ : Env N 3 := ⟨Fin.cases R (Fin.cases b (fun _ => a)), fun _ => a⟩
    exact (rd_entry0_sat_l (rt_model_ext_l hE hX hn) ρ (.bound 2) (.bound 1) .newest).symm.trans
      ((rt_model_delta_l hX hn (rd_entry0_delta_l ..) ρ).trans (rd_entry0_sat_l hE ..))
  have sub (Y : N.Domain) : N.MemberSubset Y A ↔ M.MemberSubset Y.val A.val :=
    ⟨fun h a ha => h ⟨a, hX Y.val Y.property a ha⟩ ha, fun h a ha => h a.val ha⟩
  constructor
  · intro hw Y hY hs ⟨a, ha⟩
    obtain ⟨b, hb, hm⟩ := hw ⟨Y, hY⟩ ((sub ⟨Y, hY⟩).mpr hs) ⟨⟨a, hX Y hY a ha⟩, ha⟩
    exact ⟨b.val, hb, fun c hc hr => hm ⟨c, hX Y hY c hc⟩ hc ((en _ b).mpr hr)⟩
  · intro hw Y hs ⟨a, ha⟩
    obtain ⟨b, hb, hm⟩ := hw Y.val Y.property ((sub Y).mp hs) ⟨a.val, ha⟩
    exact ⟨⟨b, hX Y.val Y.property b hb⟩, hb, fun c hc hr => hm c.val hc ((en c _).mp hr)⟩

theorem sc_collapse_sat_l (hE : Extensional M) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x : M.Domain // M.mem x X}) (ρ : Env (rt_model_l X hn) 0) :
    Formula.satisfies ρ sc_collapse_m ↔ Sc_collapse_d X := by
  have wf (η : Env (rt_model_l X hn) 2) :
      Formula.satisfies η (wf_rel_m (.bound 1) .newest) ↔ Sc_wf_d X (η.bound 1).val (η.bound 0).val :=
    (wf_rel_sat_l (rt_model_ext_l hE hX hn) η _ _).trans (sc_wf_relative_l hE hX hn _ _)
  have cert (η : Env (rt_model_l X hn) 4) :
      Formula.satisfies η (wc_map_m (.bound 3) (.bound 2) (.bound 1) .newest) ↔
        Wc_map_d (η.bound 3).val (η.bound 2).val (η.bound 1).val (η.bound 0).val :=
    (rt_model_delta_l hX hn (wc_map_delta_l ..) η).trans (wc_map_sat_l hE ..)
  simp only [sc_collapse_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, wf, cert]
  constructor
  · intro h A R hA hR hw
    obtain ⟨B, F, hf⟩ := h ⟨A, hA⟩ ⟨R, hR⟩ hw
    exact ⟨B.val, F.val, B.property, F.property, hf⟩
  · intro h A R hw
    obtain ⟨B, F, hB, hF, hf⟩ := h A.val R.val A.property R.property hw
    exact ⟨⟨B, hB⟩, ⟨F, hF⟩, hf⟩

theorem sc_h_collapse_l (hZFC : M.Models ZFC) {ω χ H : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H) : Sc_collapse_d H := by
  intro A R hA _ hw
  exact ZFC.h_collapse_l hZFC hω hχ hωχ hH hA
    (fun Y hs => hw Y (ZF.h_subsets_l _ (ZFC.models_zf_l hZFC) hχ.isLimitOrdinal hH hA Y hs) hs)

/-- 传输封闭句子而非逐个旧参数，目标中的任意新关系都能直接调用。 -/
theorem Sc_collapse_d.map_l (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (h : Sc_collapse_d X) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hq : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y q) : Sc_collapse_d Y := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  obtain ⟨y, hy⟩ := hn.1.2.1
  let nx : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨y, hy⟩⟩
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  let η : Env (rt_model_l Y ny) 0 := ⟨Fin.elim0, fun _ => ⟨y, hy⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ he, hn.empty_pred_l _ he, hq⟩ nx ny
    sc_collapse_m (by simp -implicitDefEqProofs [sc_collapse_m, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)
  exact (sc_collapse_sat_l hZF.1 hY ny η).mp (tr.mp ((sc_collapse_sat_l hZF.1 hX nx ρ).mpr h))

/-- 背景良基性蕴含相对良基性，故实际关系的塌缩可直接在源中计算。 -/
theorem Sc_collapse_d.collapse_l (hZF : M.Models ZF) {X A R : M.Domain} (h : Sc_collapse_d X)
    (hA : M.mem A X) (hR : M.mem R X) (hw : Wf_rel_d A R) (he : Wc_ext_d A R) :
    ∃ B F, M.mem B X ∧ M.mem F X ∧ Wc_iso_d A R B F := by
  obtain ⟨B, F, hB, hF, hg⟩ := h A R hA hR (fun Y _ => hw Y)
  exact ⟨B, F, hB, hF, hg.iso_l hZF he⟩

/-- 内部塌缩图的 Δ₀ 证书反映任意关系的良基性，无须关系外延或外部封闭。 -/
theorem Sc_collapse_d.wf_absolute_l (hKP : M.Models KP) {X A R : M.Domain} (h : Sc_collapse_d X)
    (hA : M.mem A X) (hR : M.mem R X) : Sc_wf_d X A R ↔ Wf_rel_d A R := by
  refine ⟨fun hw => ?_, fun hw Y _ => hw Y⟩
  obtain ⟨_, _, _, _, hc⟩ := h A R hA hR hw
  exact hc.well_founded_l hKP

end YesMetaZFC.SetTheory.Internal
