import YesMetaZFC.Model.SetTheory.Internal.SourceAlgebra
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 源内单射图的限制证书

图在指定集合 A 上取唯一的序数值并保持单射；允许图还定义其他点。
因此同一实际图直接控制 A 的任意子集。背景大小界由有界图分离得到。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Sc_index_d (μ A f : M.Domain) : Prop where
  ordinal : M.IsOrdinal μ
  total : ∀ a, M.mem a A → ∃ b, M.mem b μ ∧ Rd_entry_d a b f
  functional : ∀ a, M.mem a A → ∀ b, M.mem b μ → ∀ c, M.mem c μ → Rd_entry_d a b f → Rd_entry_d a c f → b = c
  injective : ∀ a, M.mem a A → ∀ b, M.mem b A → ∀ c, M.mem c μ → Rd_entry_d a c f → Rd_entry_d b c f → a = b

def sc_index_m {n} (μ A f : Term n) : Formula 1 n := .conj (KP.ord0_m μ) (.conj (sc_total0_m A μ f)
  (.conj (Formula.forallMem A (Formula.forallMem μ.weaken (Formula.forallMem μ.weaken.weaken
    (.imp (rd_entry0_m (.bound 2) (.bound 1) f.weaken.weaken.weaken)
      (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken) (Formula.extensionalEq (.bound 1) .newest))))))
    (Formula.forallMem A (Formula.forallMem A.weaken (Formula.forallMem μ.weaken.weaken
      (.imp (rd_entry0_m (.bound 2) .newest f.weaken.weaken.weaken)
        (.imp (rd_entry0_m (.bound 1) .newest f.weaken.weaken.weaken) (Formula.extensionalEq (.bound 2) (.bound 1)))))))))
derive_free_closed sc_index_m

theorem sc_index_delta_l {n} (μ A f : Term n) : (sc_index_m μ A f).IsDelta0 :=
  .conj (KP.ord0_delta_l _) (.conj (sc_total0_delta_l ..)
    (.conj (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom ..))))))
      (.forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (.atom ..))))))))

theorem sc_index_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (μ A f : Term n) :
    Formula.satisfies ρ (sc_index_m μ A f) ↔ Sc_index_d (μ.eval ρ) (A.eval ρ) (f.eval ρ) := by
  simp only [sc_index_m, Formula.satisfies_conj_iff, KP.ord0_sat_l hKP, sc_total0_sat_l hKP.1,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l hKP.1,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨ho, ht, hf, hi⟩ => ⟨ho, ht, hf, hi⟩, fun h => ⟨h.ordinal, h.total, h.functional, h.injective⟩⟩

theorem Sc_index_d.of_injection_l (hKP : M.Models KP) {μ A f : M.Domain} (hμ : M.IsOrdinal μ)
    (hf : M.IsSetInjectionFromTo (kp_pair_l hKP) f A μ) : Sc_index_d μ A f :=
  ⟨hμ, hf.1.2.2, fun a _ b _ c _ => hf.1.1.2 a b c, fun a _ b _ c _ => hf.2 a b c⟩

theorem Sc_index_d.bound_l (hKP : M.Models KP) {μ A f : M.Domain} (h : Sc_index_d μ A f) :
    M.CardinalLessOrEqual (kp_pair_l hKP) A μ := by
  let φ : Delta0BinarySchema 2 := {
    body := .conj (.mem .newest (.bound 2)) (rd_entry0_m (.bound 1) .newest (.bound 3))
    delta0 := .conj (.mem _ _) (rd_entry0_delta_l ..) }
  let ρ : Env M 2 := ⟨Fin.cases μ (fun _ => f), fun _ => f⟩
  have sat a b : (S1_binary.of_delta0 φ).schema.denote ρ a b ↔ M.mem b μ ∧ Rd_entry_d a b f := by
    rw [S1_binary.of_delta0_sat_l]
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hKP.1]; rfl
  obtain ⟨g, hg, spec⟩ := s1_function_l hKP (S1_binary.of_delta0 φ) ρ A μ
    (fun a ha => (h.total a ha).imp fun b hb => (sat a b).mpr hb)
    (fun a ha b c hb hc => h.functional a ha b ((sat a b).mp hb).1 c ((sat a c).mp hc).1
      ((sat a b).mp hb).2 ((sat a c).mp hc).2)
    (fun a _ b hb => ((sat a b).mp hb).1)
  exact ⟨g, fn0_function_l hKP hg, fun a b c ha hb => h.injective a (hg.bound_l ha).1 b (hg.bound_l hb).1
    c (hg.bound_l ha).2 ((sat a c).mp ((spec a c).mp ha).2).2 ((sat b c).mp ((spec b c).mp hb).2).2⟩

def Sc_small_d (X A : M.Domain) : Prop := ∃ μ f, M.mem μ X ∧ M.mem f X ∧ Sc_index_d μ A f

def sc_small_m {n} (A : Term n) : Formula 1 n :=
  .existsE (.existsE (sc_index_m (.bound 1) A.weaken.weaken .newest))
derive_free_closed sc_small_m

theorem Sc_small_d.mono_l {X A B : M.Domain} (h : Sc_small_d X A) (hBA : M.MemberSubset B A) : Sc_small_d X B := by
  obtain ⟨μ, f, hμ, hf, idx⟩ := h
  exact ⟨μ, f, hμ, hf, idx.ordinal, fun b hb => idx.total b (hBA b hb),
    fun a ha => idx.functional a (hBA a ha), fun a ha b hb => idx.injective a (hBA a ha) b (hBA b hb)⟩

theorem sc_small_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hx : Nonempty {x // M.mem x X}) {n} (ρ : Env (rt_model_l X hx) n) (A : Term n) :
    Formula.satisfies ρ (sc_small_m A) ↔ Sc_small_d X (A.eval ρ).val := by
  have matrix (η : Env (rt_model_l X hx) (n+2)) :
      Formula.satisfies η (sc_index_m (.bound 1) A.weaken.weaken .newest) ↔
        Sc_index_d (η.bound 1).val (A.weaken.weaken.eval η).val (η.bound 0).val := by
    have tr := (rt_model_delta_l hX hx (sc_index_delta_l (.bound 1) A.weaken.weaken .newest) η).trans (sc_index_sat_l hKP ..)
    cases A <;> exact tr
  simp only [sc_small_m, Formula.satisfies_exists_iff, matrix, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨μ, f, h⟩ => ⟨μ.val, f.val, μ.property, f.property, h⟩,
    fun ⟨μ, f, hμ, hf, h⟩ => ⟨⟨μ, hμ⟩, ⟨f, hf⟩, h⟩⟩

theorem sc_h_small_l (hZFC : M.Models ZFC) {ω χ X A : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hX : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ X) (hA : M.mem A X) : Sc_small_d X A := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨μ, hμ, f, hf⟩ := ZF.hmem_size_l I hZF ((hX A).mp hA)
  have hμX := ZF.h_ordinal_l I hZF hχ.isLimitOrdinal hX hμ
  exact ⟨μ, f, hμX, ZFC.h_function_l hZFC hω hχ hωχ hX hA
    ⟨hf.1.1, hf.1.2.1, fun a ha => (hf.1.2.2 a ha).imp fun b hb =>
      ⟨ZF.h_transitive_l I hZF hX μ hμX b hb.1, hb.2⟩⟩,
    Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hχ.isCardinal.1.mem hμ) hf⟩

theorem Smap_d.small_l (hZF : M.Models ZF) {ω c d X R Y S j A B : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R) (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y j) (hAB : Rd_entry_d A B j) : Sc_small_d X A ↔ Sc_small_d Y B := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let a := (⟨A, hj.1.1.input_mem_of_pairMember hAB⟩ : {a // M.mem a X})
  let b := (⟨B, hj.1.1.output_mem_of_pairMember hAB⟩ : {b // M.mem b Y})
  let ρ : Env (rt_model_l X ⟨a⟩) 1 := ⟨fun _ => a, fun _ => a⟩
  let η : Env (rt_model_l Y ⟨b⟩) 1 := ⟨fun _ => b, fun _ => b⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I he, hn.empty_pred_l I he, hj⟩ ⟨a⟩ ⟨b⟩
    (sc_small_m .newest) (by simp -implicitDefEqProofs) ρ η (fun _ => hAB)
  exact (sc_small_sat_l (ZF.modelsKP hZF) hX ⟨a⟩ ρ .newest).symm.trans
    (tr.trans (sc_small_sat_l (ZF.modelsKP hZF) hY ⟨b⟩ η .newest))

theorem sc_ordinal_small_l (hZF : M.Models ZF) {ω c X R A : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R) (hA : M.mem A X)
    (ho : M.IsOrdinal A) : Sc_small_d X A := by
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => A⟩
  have sat a b : φ.denote ρ a b ↔ a = b := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨f, hf, fn, eq⟩ := sc_uniform_source_l hZF hω hX hm theory φ (.atom ..) ρ (fun i => Fin.elim0 i) hA hA
    (fun a ha => ⟨a, ha, (sat a a).mpr rfl⟩)
  exact ⟨A, f, hA, hf, Sc_index_d.of_injection_l (ZF.modelsKP hZF) ho
    ⟨fn0_function_l (ZF.modelsKP hZF) fn, fun a b y ha hb => ((sat a y).mp (eq a y ha)).trans ((sat b y).mp (eq b y hb)).symm⟩⟩

/-- 源内满射的像仍由源内实际单射控制；不要求满射本身是单射。 -/
theorem sc_index_image_l (hZF : M.Models ZF) {ω c X R μ e A B q : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hA : M.mem A X) (hB : M.mem B X) (hq : M.mem q X)
    (hμ : M.mem μ X) (he : M.mem e X) (idx : Sc_index_d μ A e)
    (fn : Fn0_d A B q) (onto : ∀ b, M.mem b B → ∃ a, M.mem a A ∧ Rd_entry_d a b q) : ∃ f, M.mem f X ∧ Sc_index_d μ B f := by
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m .newest (.bound 2) (.bound 3)) (rd_entry0_m .newest (.bound 1) (.bound 4))) }
  let ρ : Env M 3 := ⟨Fin.cases q (Fin.cases e (fun _ => A)), fun _ => A⟩
  have sat b y : φ.denote ρ b y ↔ ∃ a, M.mem a A ∧ Rd_entry_d a b q ∧ Rd_entry_d a y e := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨f, hf, hfn, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))) ρ (Fin.cases hq (Fin.cases he (fun _ => hA))) hB hμ
    (fun b hb => by
      obtain ⟨a, ha, hab⟩ := onto b hb
      obtain ⟨y, hy, hay⟩ := idx.total a ha
      exact ⟨y, hy, (sat b y).mpr ⟨a, ha, hab, hay⟩⟩)
  refine ⟨f, hf, Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal ⟨fn0_function_l (ZF.modelsKP hZF) hfn, ?_⟩⟩
  intro b c y hb hc
  obtain ⟨a, ha, hab, hay⟩ := (sat b y).mp (select b y hb)
  obtain ⟨d, hd, hdc, hdy⟩ := (sat c y).mp (select c y hc)
  have eq := idx.injective a ha d hd y (hfn.bound_l hb).2 hay hdy
  subst d
  exact (fn0_function_l (ZF.modelsKP hZF) fn).1.2 a b c hab hdc

theorem sc_small_image_l (hZF : M.Models ZF) {ω c X R A B q : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hA : M.mem A X) (hB : M.mem B X) (hq : M.mem q X) (small : Sc_small_d X A)
    (fn : Fn0_d A B q) (onto : ∀ b, M.mem b B → ∃ a, M.mem a A ∧ Rd_entry_d a b q) : Sc_small_d X B := by
  obtain ⟨μ, e, hμ, he, idx⟩ := small
  obtain ⟨f, hf, hi⟩ := sc_index_image_l hZF hω hX hm theory hA hB hq hμ he idx fn onto
  exact ⟨μ, f, hμ, hf, hi⟩

/-- 小性的回拉只用源内单射，无须字母表本身是序数。 -/
theorem sc_small_pull_l (hZF : M.Models ZF) {ω c X R A B p : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hA : M.mem A X) (hB : M.mem B X) (hp : M.mem p X) (small : Sc_small_d X B)
    (inj : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) p A B) : Sc_small_d X A := by
  obtain ⟨μ, e, hμ, he, idx⟩ := small
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 4)
      (.conj (rd_entry0_m (.bound 2) .newest (.bound 3)) (rd_entry0_m .newest (.bound 1) (.bound 4))) }
  let ρ : Env M 3 := ⟨Fin.cases p (Fin.cases e (fun _ => B)), fun _ => B⟩
  have sat a y : φ.denote ρ a y ↔ ∃ b, M.mem b B ∧ Rd_entry_d a b p ∧ Rd_entry_d b y e := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨f, hf, hfn, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))) ρ (Fin.cases hp (Fin.cases he (fun _ => hB))) hA hμ
    (fun a ha => by
      obtain ⟨b, hb, hab⟩ := inj.1.2.2 a ha
      obtain ⟨y, hy, hby⟩ := idx.total b hb
      exact ⟨y, hy, (sat a y).mpr ⟨b, hb, hab, hby⟩⟩)
  refine ⟨μ, f, hμ, hf, Sc_index_d.of_injection_l (ZF.modelsKP hZF) idx.ordinal ⟨fn0_function_l (ZF.modelsKP hZF) hfn, ?_⟩⟩
  intro a c y ha hc
  obtain ⟨b, hb, hab, hby⟩ := (sat a y).mp (select a y ha)
  obtain ⟨d, hd, hcd, hdy⟩ := (sat c y).mp (select c y hc)
  have eq := idx.injective b hb d hd y (hfn.bound_l ha).2 hby hdy
  subst d
  exact inj.2 a c b hab hcd

/-- 将已有的部分编号限制到指定定义域，实际图仍在源中。 -/
theorem Sc_index_d.restrict_l (hZF : M.Models ZF) {ω c X R μ A e : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hA : M.mem A X) (hμ : M.mem μ X) (he : M.mem e X) (idx : Sc_index_d μ A e) :
    ∃ f, M.mem f X ∧ M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f A μ := by
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 1) .newest (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => e, fun _ => e⟩
  have sat x y : φ.denote ρ x y ↔ Rd_entry_d x y e := rd_entry0_sat_l hZF.1 ..
  obtain ⟨f, hf, fn, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ (rd_entry0_delta_l ..) ρ
    (fun _ => he) hA hμ (fun x hx => (idx.total x hx).imp fun y hy => ⟨hy.1, (sat x y).mpr hy.2⟩)
  exact ⟨f, hf, fn0_function_l (ZF.modelsKP hZF) fn, fun a b y ha hb =>
    idx.injective a (fn.bound_l ha).1 b (fn.bound_l hb).1 y (fn.bound_l ha).2
      ((sat a y).mp (select a y ha)) ((sat b y).mp (select b y hb))⟩

/-- 任意源内小集合可用一个包含 ω 的源内序数编号。 -/
theorem sc_infinite_index_l (hZF : M.Models ZF) {ω c X R A : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R) (hωX : M.mem ω X) (hA : M.mem A X)
    (small : Sc_small_d X A) : ∃ μ f, M.mem μ X ∧ M.mem f X ∧ M.MemberSubset ω μ ∧ Sc_index_d μ A f := by
  obtain ⟨μ, e, hμ, he, idx⟩ := small
  obtain ⟨f, hf, inj⟩ := idx.restrict_l hZF hω hX hm theory hA hμ he
  rcases idx.ordinal.trichotomy hZF.1 (hω.isOrdinal hZF) (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) μ ω) with eq | lt | gt
  · exact ⟨μ, e, hμ, he, fun x hx => (eq x).mpr hx, idx⟩
  · exact ⟨ω, f, hωX, hf, fun _ h => h, Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal hZF)
      ⟨inj.1.mono_target_l _ ((hω.isOrdinal hZF).transitive μ lt), inj.2⟩⟩
  · exact ⟨μ, e, hμ, he, idx.ordinal.transitive ω gt, idx⟩

end YesMetaZFC.SetTheory.Internal
