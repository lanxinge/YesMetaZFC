import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.SetTheory.HereditaryCollapse
import YesMetaZFC.Model.SetTheory.Source.CollectionBasis
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.Model.SetTheory.Source.Relation

/-! # 塌缩存在句子的源模型闭包与初等保持

小关系及其坍塌图直接在原关系中解释，整条闭合句子沿实际初等图双向传递。
Hχ、Vδ 的原实例通过实际隶属码读取；其子集闭包把相对良基性提升为背景良基性。
新目标不需要背景传递性或原生 ZF，坍塌结果仍是该关系模型自己的对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_wf_d (X A R : M.Domain) : Prop :=
  ∀ Y, M.mem Y X → M.MemberSubset Y A → (∃ a, M.mem a Y) →
    ∃ a, M.mem a Y ∧ ∀ b, M.mem b Y → ¬ Rd_entry_d b a R

def sc_collapse_m : Formula 1 0 := .forallE (.forallE
  (.imp (sc_small_m (.bound 1)) (.imp (wf_rel_m (.bound 1) .newest) (.imp (wc_ext_m (.bound 1) .newest)
    (.existsE (.existsE (wc_iso_m (.bound 3) (.bound 2) (.bound 1) .newest)))))))

theorem sc_collapse_closed_l : sc_collapse_m.FreeClosed := by
  simp -implicitDefEqProofs [sc_collapse_m, Definitional.Formula.FreeClosed]

/-- 小性、相对良基性和坍塌图均在同一个原关系模型内判断。 -/
def Sc_collapse_d {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (X R : M.Domain) : Prop :=
  ∀ nx : ∃ x, M.mem x X, ∀ ρ : Env (smdl_structure_l I (R := R) nx) 0,
    Formula.satisfies ρ sc_collapse_m

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

theorem sc_collapse_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hn : Nonempty {x : M.Domain // M.mem x X}) (ρ : Env (rt_model_l X hn) 0) :
    Formula.satisfies ρ sc_collapse_m ↔
      ∀ A R, M.mem A X → M.mem R X → Sc_small_d X A → Sc_wf_d X A R → Wc_ext_d A R →
        ∃ B F, M.mem B X ∧ M.mem F X ∧ Wc_iso_d A R B F := by
  have wf (η : Env (rt_model_l X hn) 2) :
      Formula.satisfies η (wf_rel_m (.bound 1) .newest) ↔ Sc_wf_d X (η.bound 1).val (η.bound 0).val :=
    (wf_rel_sat_l (rt_model_ext_l hKP.1 hX hn) η _ _).trans (sc_wf_relative_l hKP.1 hX hn _ _)
  have ext (η : Env (rt_model_l X hn) 2) :
      Formula.satisfies η (wc_ext_m (.bound 1) .newest) ↔ Wc_ext_d (η.bound 1).val (η.bound 0).val :=
    (rt_model_delta_l hX hn (wc_ext_delta_l ..) η).trans (wc_ext_sat_l hKP.1 ..)
  have cert (η : Env (rt_model_l X hn) 4) :
      Formula.satisfies η (wc_iso_m (.bound 3) (.bound 2) (.bound 1) .newest) ↔
        Wc_iso_d (η.bound 3).val (η.bound 2).val (η.bound 1).val (η.bound 0).val :=
    (rt_model_delta_l hX hn (wc_iso_delta_l ..) η).trans (wc_iso_sat_l hKP.1 ..)
  simp only [sc_collapse_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, sc_small_sat_l hKP hX hn, wf, ext, cert]
  constructor
  · intro h A R hA hR small hw he
    obtain ⟨B, F, hf⟩ := h ⟨A, hA⟩ ⟨R, hR⟩ small hw he
    exact ⟨B.val, F.val, B.property, F.property, hf⟩
  · intro h A R small hw he
    obtain ⟨B, F, hB, hF, hf⟩ := h A.val R.val A.property R.property small hw he
    exact ⟨⟨B, hB⟩, ⟨F, hF⟩, hf⟩

/-- 实际传递隶属实例读取原关系中的小坍塌句子。 -/
theorem sc_collapse_mem_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hKP : M.Models KP)
    {c X R : M.Domain} (trans : M.TransitiveSet X) (model : Smem_d I c X R) :
    Sc_collapse_d I X R ↔
      ∀ A S, M.mem A X → M.mem S X → Sc_small_d X A → Sc_wf_d X A S → Wc_ext_d A S →
        ∃ B F, M.mem B X ∧ M.mem F X ∧ Wc_iso_d A S B F := by
  obtain ⟨x, hx⟩ := model.1.2.1
  let nx : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  constructor
  · intro h
    let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
    exact (sc_collapse_sat_l hKP trans nx ρ).mp
      ((smem_formula_l I model nx sc_collapse_m ρ).mpr (h model.1.2.1 ⟨ρ.bound, ρ.free⟩))
  · intro h ny η
    let ρ : Env (rt_model_l X nx) 0 := ⟨η.bound, η.free⟩
    exact (smem_formula_l I model nx sc_collapse_m ρ).mp ((sc_collapse_sat_l hKP trans nx ρ).mpr h)

theorem sc_h_collapse_l (hZFC : M.Models ZFC) {ω χ H : M.Domain}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ)
    (hωχ : M.mem ω χ) (hH : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ H)
    {c R : M.Domain} (model : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c H R) :
    Sc_collapse_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) H R := by
  apply (sc_collapse_mem_l _ (ZF.modelsKP (ZFC.models_zf_l hZFC)) (ZF.h_transitive_l _ (ZFC.models_zf_l hZFC) hH) model).mpr
  intro A T hA _ _ hw he
  obtain ⟨B, F, hB, hF, iso⟩ := ZFC.h_collapse_l hZFC hω hχ hωχ hH hA
    (fun Y hs => hw Y (ZF.h_subsets_l _ (ZFC.models_zf_l hZFC) hχ.isLimitOrdinal hH hA Y hs) hs)
  exact ⟨B, F, hB, hF, iso.iso_l (ZFC.models_zf_l hZFC) he⟩

theorem sc_v_collapse_l (hZF : M.Models ZF) {δ V : M.Domain}
    (hδ : M.IsCardinal (kp_pair_l (ZF.modelsKP hZF)) δ) (hl : M.IsLimitOrdinal δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ V)
    {c R : M.Domain} (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c V R) :
    Sc_collapse_d (kp_pair_l (ZF.modelsKP hZF)) V R := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (sc_collapse_mem_l I (ZF.modelsKP hZF) (v_transitive_l I hV) model).mpr
  intro A T hA _ small hw he
  obtain ⟨B, F, iso⟩ := wc_iso_exists_l hZF (fun Y hs => hw Y (v_subset_mem_l I hV hA hs) hs) he
  obtain ⟨μ, f, hμ, _, idx⟩ := small
  obtain ⟨g, hg⟩ := idx.bound_l (ZF.modelsKP hZF)
  obtain ⟨q, hq, _⟩ := ZF.exists_inverseBijectionWithPairs hZF I (iso.bijection_l (ZF.modelsKP hZF))
  obtain ⟨T, ν, tc, hν, size⟩ := ZF.hmem_of_subset_l I hZF hl iso.transitive (fun _ h => h)
    (ZF.v_ordinal_height_l hZF hV idx.ordinal hμ) (ZF.exists_compositionInjection hZF I hq.1 hg)
  have hB := ZF.rk_transitive_bound_l I hZF tc.1 hδ hν size hV B tc.2.1
  obtain ⟨Y, hY, hAY, hBY⟩ := v_joint_bound_l I hV hA hB
  exact ⟨B, F, hB, v_relation_mem_l I hV hl hY (fun p hp =>
    (iso.function.1 p hp).elim fun a ha => ha.2.elim fun b hb => ⟨a, hAY a ha.1, b, hBY b hb.1, hb.2⟩), iso⟩

/-- 整个原关系句子双向传递，目标中新出现的小关系也得到实际坍塌图。 -/
theorem sc_collapse_iff_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {ω c d X R Y S q : M.Domain} (hω : M.IsOmega ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I ω c d X Y q) :
    Sc_collapse_d I X R ↔ Sc_collapse_d I Y S := by
  obtain ⟨x, hx⟩ := mx.2.1
  obtain ⟨y, hy⟩ := my.2.1
  let ρ : Env (smdl_structure_l I (R := R) mx.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  let η : Env (smdl_structure_l I (R := S) my.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨y, hy⟩⟩
  exact ⟨fun h _ θ => (smap_source_l I hZF hω mx my map sc_collapse_m sc_collapse_closed_l
    ρ θ (fun i => Fin.elim0 i)).mp (h mx.2.1 ρ),
    fun h _ θ => (smap_source_l I hZF hω mx my map sc_collapse_m sc_collapse_closed_l
      θ η (fun i => Fin.elim0 i)).mpr (h my.2.1 η)⟩

/-- 背景良基性蕴含相对良基性；只在实际隶属实例中读取背景坍塌图。 -/
theorem Sc_collapse_d.collapse_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hKP : M.Models KP)
    {c X S A R : M.Domain} (trans : M.TransitiveSet X) (model : Smem_d I c X S) (h : Sc_collapse_d I X S)
    (hA : M.mem A X) (hR : M.mem R X) (small : Sc_small_d X A) (hw : Wf_rel_d A R) (he : Wc_ext_d A R) :
    ∃ B F, M.mem B X ∧ M.mem F X ∧ Wc_iso_d A R B F :=
  (sc_collapse_mem_l I hKP trans model).mp h A R hA hR small (fun Y _ => hw Y) he

end YesMetaZFC.SetTheory.Internal

/-! ## 源内小关系的传递像及求值图

呈示允许重复代表：以各点的前驱集作商，传递像的外延性恰好识别这些纤维。
商关系、商投影及其小性都在源内构造，再用原塌缩闭包和唯一性还原同一个像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_presentation_l {ω c X R A Q B e : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collapse : Sc_collapse_d I X R)
    (hA : M.mem A X) (hQ : M.mem Q X) (small : Sc_small_d X A) (relation : M.IsSetRelationOn I Q A)
    (hB : M.TransitiveSet B) (he : Fn0_d A B e) (onto : ∀ x, M.mem x B → ∃ a, M.mem a A ∧ Rd_entry_d a x e)
    (member : ∀ a b x y, Rd_entry_d a x e → Rd_entry_d b y e → (Rd_entry_d a b Q ↔ M.mem x y)) :
    M.mem B X ∧ M.mem e X := by
  obtain ⟨q, _, hq, _, hqf, qs⟩ := sc_fiber_function_l hZF hω hX hm theory hA hQ
  obtain ⟨C, hC, range⟩ := sc_range_source_l hZF hω hX hm theory hq
  have hqf := hqf.retarget_l (fun a E ha => (range E).mpr ⟨a, ha⟩)
  have qonto E (hE : M.mem E C) : ∃ a, M.mem a A ∧ Rd_entry_d a E q := by
    obtain ⟨a, ha⟩ := (range E).mp hE
    exact ⟨a, (hqf.bound_l ha).1, ha⟩
  have kernel a b E H x y (ha : Rd_entry_d a E q) (hb : Rd_entry_d b H q)
      (hx : Rd_entry_d a x e) (hy : Rd_entry_d b y e) : E = H ↔ x = y := by
    have left := ((qs a E).mp ha).2
    have right := ((qs b H).mp hb).2
    constructor
    · intro eq
      apply hZF.1.eq_of_same_members x y
      intro z
      have forward a b E H x y (left : Rd_fiber_d Q a E) (right : Rd_fiber_d Q b H)
          (hx : Rd_entry_d a x e) (hy : Rd_entry_d b y e) (eq : E = H) (hz : M.mem z x) : M.mem z y := by
        obtain ⟨u, _, huz⟩ := onto z (hB x (he.bound_l hx).2 z hz)
        exact (member u b z y huz hy).mp ((right u).mp (eq ▸ (left u).mpr ((member u a z x huz hx).mpr hz)))
      exact ⟨forward a b E H x y left right hx hy eq, forward b a H E y x right left hy hx eq.symm⟩
    · intro eq
      apply hZF.1.eq_of_same_members E H
      intro u
      have compare a b x y (hx : Rd_entry_d a x e) (hy : Rd_entry_d b y e) (eq : x = y)
          (hu : Rd_entry_d u a Q) : Rd_entry_d u b Q := by
        obtain ⟨z, _, huz⟩ := he.2.1 u (relation.2 u a hu).1
        exact (member u b z y huz hy).mpr (eq ▸ (member u a z x huz hx).mp hu)
      exact (left u).trans ((Iff.intro (compare a b x y hx hy eq) (compare b a y x hy hx eq.symm)).trans (right u).symm)
  let ρ : Env M 3 := ⟨Fin.cases e (Fin.cases q (fun _ => A)), fun _ => A⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m .newest (.bound 2) (.bound 4)) (rd_entry0_m .newest (.bound 1) (.bound 3))) }
  have sat E x : φ.denote ρ E x ↔ ∃ a, M.mem a A ∧ Rd_entry_d a E q ∧ Rd_entry_d a x e := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨g, hg, gs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := C) (target := B)
    (fun E hE => by
      obtain ⟨a, ha, haE⟩ := qonto E hE
      obtain ⟨x, _, hax⟩ := he.2.1 a ha
      exact ⟨x, (sat E x).mpr ⟨a, ha, haE, hax⟩⟩)
    (fun E _ x y hx hy => by
      obtain ⟨a, _, haE, hax⟩ := (sat E x).mp hx
      obtain ⟨b, _, hbE, hby⟩ := (sat E y).mp hy
      exact (kernel a b E E x y haE hbE hax hby).mp rfl)
    (fun _ x _ hx => ((sat _ x).mp hx).elim fun _ ha => (he.bound_l ha.2.2).2)
  have gspec E x := (gs E x).trans (and_congr_right fun _ => sat E x)
  let η : Env M 3 := ⟨Fin.cases Q (Fin.cases q (fun _ => A)), fun _ => A⟩
  let ψ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 4) (Formula.existsMem (.bound 5)
      (.conj (rd_entry0_m (.bound 1) (.bound 3) (.bound 5)) (.conj
        (rd_entry0_m .newest (.bound 2) (.bound 5)) (rd_entry0_m (.bound 1) .newest (.bound 4))))) }
  have sat' E H : ψ.denote η E H ↔ ∃ a, M.mem a A ∧ ∃ b, M.mem b A ∧
      Rd_entry_d a E q ∧ Rd_entry_d b H q ∧ Rd_entry_d a b Q := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨S, hS, _, ss⟩ := sc_relation_source_l hZF hω hX hm theory ψ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))
    η (Fin.cases hQ (Fin.cases hq (fun _ => hA))) hC hC
  have iso : Wc_iso_d C S B g := by
    refine ⟨hB, fn0_of_function_l (ZF.modelsKP hZF) hg, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, hax⟩ := onto x hx
      obtain ⟨E, hE, haE⟩ := hqf.2.1 a ha
      exact ⟨E, hE, (gs E x).mpr ⟨hE, (sat E x).mpr ⟨a, ha, haE, hax⟩⟩⟩
    · intro E _ H _ x _ he' hh'
      obtain ⟨_, a, _, haE, hax⟩ := (gspec E x).mp he'
      obtain ⟨_, b, _, hbH, hbx⟩ := (gspec H x).mp hh'
      exact (kernel a b E H x x haE hbH hax hbx).mpr rfl
    · intro E hE H hH x _ y _ he' hh'
      obtain ⟨_, a, ha, haE, hax⟩ := (gspec E x).mp he'
      obtain ⟨_, b, hb, hbH, hby⟩ := (gspec H y).mp hh'
      rw [ss E H, sat' E H]
      refine ⟨?_, fun hxy => ⟨hE, hH, a, ha, b, hb, haE, hbH, (member a b x y hax hby).mpr hxy⟩⟩
      rintro ⟨_, _, a', ha', b', hb', ha'E, hb'H, edge⟩
      obtain ⟨x', _, ha'x⟩ := he.2.1 a' ha'
      obtain ⟨y', _, hb'y⟩ := he.2.1 b' hb'
      exact (kernel a' a E E x' x ha'E haE ha'x hax).mp rfl ▸
        (kernel b' b H H y' y hb'H hbH hb'y hby).mp rfl ▸ (member a' b' x' y' ha'x hb'y).mp edge
  have small' := sc_small_image_l hZF hω hX hm theory hA hC hq small hqf qonto
  obtain ⟨B', g', hB', hg', iso'⟩ := collapse.collapse_l I (ZF.modelsKP hZF) hX hm hC hS small' (iso.well_founded_l (ZF.modelsKP hZF)) (iso.extensional_l hZF.1)
  have eB := iso'.unique_l hZF iso
  have eg := iso'.graph_unique_l hZF iso
  subst B' g'
  let ξ : Env M 3 := ⟨Fin.cases g (Fin.cases q (fun _ => C)), fun _ => C⟩
  let χ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 4)) (rd_entry0_m .newest (.bound 1) (.bound 3))) }
  have comp a x : χ.denote ξ a x ↔ ∃ E, M.mem E C ∧ Rd_entry_d a E q ∧ Rd_entry_d E x g := by
    simp only [χ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨f, hf, fn, fs⟩ := sc_uniform_source_l hZF hω hX hm theory χ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))) ξ
    (Fin.cases hg' (Fin.cases hq (fun _ => hC))) hA hB' (fun a ha => by
      obtain ⟨E, hE, haE⟩ := hqf.2.1 a ha
      obtain ⟨x, hx, hEx⟩ := hg.2.2 E hE
      exact ⟨x, hx, (comp a x).mpr ⟨E, hE, haE, hEx⟩⟩)
  have eq := fn.ext_l hZF.1 he (fun a ha => by
    obtain ⟨x, _, hax⟩ := fn.2.1 a ha
    obtain ⟨E, _, haE, hEx⟩ := (comp a x).mp (fs a x hax)
    obtain ⟨_, b, _, hbE, hbx⟩ := (gspec E x).mp hEx
    obtain ⟨y, _, hay⟩ := he.2.1 a ha
    exact ⟨x, hax, ((kernel b a E E x y hbE haE hbx hay).mp rfl).symm ▸ hay⟩)
  exact ⟨hB', eq ▸ hf⟩

end YesMetaZFC.SetTheory.Internal
