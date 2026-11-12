import YesMetaZFC.Model.SetTheory.Source.Theory
import YesMetaZFC.SetTheory.KP.Ordinal
import YesMetaZFC.SetTheory.HereditaryFunction
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.Internal.UniversalClosure
import YesMetaZFC.Model.SetTheory.Internal.Uniformization

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

theorem Sc_index_d.mono_l {μ A B f : M.Domain} (h : Sc_index_d μ A f)
    (sub : M.MemberSubset B A) : Sc_index_d μ B f :=
  ⟨h.ordinal, fun b hb => h.total b (sub b hb), fun b hb => h.functional b (sub b hb),
    fun b hb c hc => h.injective b (sub b hb) c (sub c hc)⟩

def Sc_small_d (X A : M.Domain) : Prop := ∃ μ f, M.mem μ X ∧ M.mem f X ∧ Sc_index_d μ A f

def sc_small_m {n} (A : Term n) : Formula 1 n :=
  .existsE (.existsE (sc_index_m (.bound 1) A.weaken.weaken .newest))
derive_free_closed sc_small_m

theorem Sc_small_d.mono_l {X A B : M.Domain} (h : Sc_small_d X A) (hBA : M.MemberSubset B A) : Sc_small_d X B := by
  obtain ⟨μ, f, hμ, hf, idx⟩ := h
  exact ⟨μ, f, hμ, hf, idx.mono_l hBA⟩

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
  rcases idx.ordinal.trichotomy hZF.1 (hω.isOrdinal (ZF.modelsKP hZF)) (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) μ ω) with eq | lt | gt
  · exact ⟨μ, e, hμ, he, fun x hx => (eq x).mpr hx, idx⟩
  · exact ⟨ω, f, hωX, hf, fun _ h => h, Sc_index_d.of_injection_l (ZF.modelsKP hZF) (hω.isOrdinal (ZF.modelsKP hZF))
      ⟨inj.1.mono_target_l _ ((hω.isOrdinal (ZF.modelsKP hZF)).transitive μ lt), inj.2⟩⟩
  · exact ⟨μ, e, hμ, he, idx.ordinal.transitive ω gt, idx⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 源内函数与其图的编号

在已有图中读取坐标，把定义域的单射编号传给函数图，或反向传回定义域。
编号的目标可以是任意源内集合；不要求它是基数或序数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_graph_numbering_l {ω c Z R μ A B ι j : M.Domain}
    (hω : M.IsOmega ω) (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R)
    (theory : Sc_theory_d I ω Z R) (hμZ : M.mem μ Z) (hA : M.mem A Z) (hB : M.mem B Z)
    (hιZ : M.mem ι Z) (hjZ : M.mem j Z) (hι : M.IsSetInjectionFromTo I ι A μ) (hj : Fn0_d A B j) :
    ∃ η, M.mem η Z ∧ M.IsSetInjectionFromTo I η j μ := by
  let ρ : Env M 3 := ⟨Fin.cases A (Fin.cases B (fun _ => ι)), fun _ => A⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
      (.conj (kpair0_m (.bound 3) (.bound 1) .newest) (rd_entry0_m (.bound 1) (.bound 2) (.bound 6)))) }
  have sat p i : φ.denote ρ p i ↔ ∃ x, M.mem x A ∧ ∃ y, M.mem y B ∧ KPair_d M p x y ∧ Rd_entry_d x i ι := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨η, hηZ, hf, select⟩ := sc_uniform_source_l hZF hω hZ hm theory φ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..))))
    ρ (Fin.cases hA (Fin.cases hB (fun _ => hιZ))) hjZ hμZ (fun p hp => by
      obtain ⟨x, hx, y, hy, hpair⟩ := hj.1 p hp
      obtain ⟨i, hi, hxi⟩ := hι.1.2.2 x hx
      exact ⟨i, hi, (sat p i).mpr ⟨x, hx, y, hy, hpair, hxi⟩⟩)
  refine ⟨η, hηZ, fn0_function_l (ZF.modelsKP hZF) hf, fun p q i hpi hqi => ?_⟩
  obtain ⟨x, _, y, _, hp, hxi⟩ := (sat p i).mp (select p i hpi)
  obtain ⟨z, _, v, _, hq, hzi⟩ := (sat q i).mp (select q i hqi)
  have eq := hι.2 x z i hxi hzi
  subst z
  have eq := (fn0_function_l (ZF.modelsKP hZF) hj).1.2 x y v
    ⟨p, hp, (hf.bound_l hpi).1⟩ ⟨q, hq, (hf.bound_l hqi).1⟩
  subst v
  exact kpair_unique_l M hZF.1 hp hq

theorem sc_domain_numbering_l {ω c Z R μ A B η j : M.Domain}
    (hω : M.IsOmega ω) (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R)
    (theory : Sc_theory_d I ω Z R) (hμZ : M.mem μ Z)
    (hηZ : M.mem η Z) (hjZ : M.mem j Z) (hη : M.IsSetInjectionFromTo I η j μ) (hj : Fn0_d A B j) :
    M.mem A Z ∧ ∃ ι, M.mem ι Z ∧ M.IsSetInjectionFromTo I ι A μ := by
  have hA := sc_function_domain_mem_l hZF hω hZ hm theory hjZ hj
  obtain ⟨C, hC, coords⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hZ hm).envelope_l hjZ
  have fn := hj.retarget_l (fun x y hxy => (coords x y hxy).2)
  let ρ : Env M 3 := ⟨Fin.cases j (Fin.cases C (fun _ => η)), fun _ => j⟩
  let φ : BinarySchema 3 := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
      (.conj (kpair0_m (.bound 1) (.bound 3) .newest) (rd_entry0_m (.bound 1) (.bound 2) (.bound 6)))) }
  have sat x i : φ.denote ρ x i ↔ ∃ p, M.mem p j ∧ ∃ y, M.mem y C ∧ KPair_d M p x y ∧ Rd_entry_d p i η := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨ι, hιZ, hf, select⟩ := sc_uniform_source_l hZF hω hZ hm theory φ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (rd_entry0_delta_l ..))))
    ρ (Fin.cases hjZ (Fin.cases hC (fun _ => hηZ))) hA hμZ (fun x hx => by
      obtain ⟨y, hy, p, hp, hpj⟩ := fn.2.1 x hx
      obtain ⟨i, hi, hpi⟩ := hη.1.2.2 p hpj
      exact ⟨i, hi, (sat x i).mpr ⟨p, hpj, y, hy, hp, hpi⟩⟩)
  refine ⟨hA, ι, hιZ, fn0_function_l (ZF.modelsKP hZF) hf, fun x z i hxi hzi => ?_⟩
  obtain ⟨p, _, y, _, hp, hpi⟩ := (sat x i).mp (select x i hxi)
  obtain ⟨q, _, v, _, hq, hqi⟩ := (sat z i).mp (select z i hzi)
  exact (kpair_injective_l M (hη.2 p q i hpi hqi ▸ hp) hq).1

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系中的小集合与编号

小性直接量化原关系中的序数及编号图。限制、初等搬运和收集共用此证书；
只有实际隶属模型的读取才使用背景 KP，不要求原关系满足 KP。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Rf_small_d (Y S a : M.Domain) : Prop := ∃ ha : M.mem a Y,
  Formula.satisfies (⟨fun _ => ⟨a, ha⟩, fun _ => ⟨a, ha⟩⟩ :
    Env (smdl_structure_l I (R := S) ⟨a, ha⟩) 1) (sc_small_m .newest)

theorem Rf_small_d.mem_l {J : 𝒞.Interpretation M} {X R A : M.Domain}
    (h : Rf_small_d J X R A) : M.mem A X := h.elim fun ha _ => ha

theorem rf_small_native_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (A : (smdl_structure_l I (R := R) nx).Domain) : Rf_small_d I X R A.val ↔
      Formula.satisfies (⟨fun _ => A, fun _ => A⟩ : Env (smdl_structure_l I (R := R) nx) 1)
        (sc_small_m .newest) :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨A.property, h⟩⟩

/-- 同一编号限制到任意原关系子集；此步不使用外延性或模型公理。 -/
theorem Rf_small_d.mono_l {X R A B : M.Domain} (h : Rf_small_d I X R A) (hB : M.mem B X)
    (sub : ∀ x, M.mem x X → M.PairMember I x B R → M.PairMember I x A R) : Rf_small_d I X R B := by
  obtain ⟨hA, valid⟩ := h
  refine ⟨hB, ?_⟩
  simp only [sc_small_m, sc_index_m, sc_total0_m, KP.ord0_m, rd_entry0_m, kpair0_m, pair0_m,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff,
    Definitional.Term.eval, Definitional.Term.newest,
    Definitional.Term.weaken, Definitional.Term.rename, Definitional.Term.bind,
    Function.comp_def, Env.push, fin_cases] at valid ⊢
  obtain ⟨μ, e, ord, total, functional, injective⟩ := valid
  have incl (x : (smdl_structure_l I (R := R) ⟨A, hA⟩).Domain) := sub x.val x.property
  exact ⟨μ, e, ord, fun x hx => total x (incl x hx),
    fun x hx => functional x (incl x hx), fun x hx y hy => injective x (incl x hx) y (incl y hy)⟩

/-- 实际隶属码中的子集限制无需重新构造编号，也不需要背景公理。 -/
theorem Rf_small_d.mono_mem_l {c X R A B : M.Domain} (h : Rf_small_d I X R A)
    (model : Smem_d I c X R) (hB : M.mem B X) (sub : M.MemberSubset B A) : Rf_small_d I X R B :=
  h.mono_l I hB (fun x hx hb => (model.2 x A).mpr ⟨hx, h.mem_l, sub x ((model.2 x B).mp hb).2.2⟩)

/-- 传递隶属实例中的原关系编号恰好是背景的小性证书。 -/
theorem rf_small_mem_l (hKP : M.Models KP) {c X R A : M.Domain}
    (trans : M.TransitiveSet X) (model : Smem_d I c X R) (hA : M.mem A X) :
    Rf_small_d I X R A ↔ Sc_small_d X A := by
  let ρ : Env (rt_model_l X ⟨⟨A, hA⟩⟩) 1 := ⟨fun _ => ⟨A, hA⟩, fun _ => ⟨A, hA⟩⟩
  exact (rf_small_native_l I model.1.2.1 ⟨A, hA⟩).trans
    ((smem_formula_l I model ⟨⟨A, hA⟩⟩ (sc_small_m .newest) ρ).symm.trans
      (sc_small_sat_l hKP trans ⟨⟨A, hA⟩⟩ ρ .newest))

/-- 实际隶属源中的序数以同一恒等图给出原关系小性。 -/
theorem sc_ordinal_small_l (hZF : M.Models ZF) {ω c X R A : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R) (hA : M.mem A X)
    (ho : M.IsOrdinal A) : Rf_small_d (kp_pair_l (ZF.modelsKP hZF)) X R A := by
  apply (rf_small_mem_l (kp_pair_l (ZF.modelsKP hZF)) (ZF.modelsKP hZF) hX hm hA).mpr
  obtain ⟨f, hf, fn, graph⟩ := sc_identity_l hZF hω hX hm theory hA
  exact ⟨A, f, hA, hf, Sc_index_d.of_injection_l (ZF.modelsKP hZF) ho
    ⟨fn0_function_l (ZF.modelsKP hZF) fn,
      fun a b y ha hb => ((graph a y).mp ha).2.trans ((graph b y).mp hb).2.symm⟩⟩

theorem Rf_small_d.index_l {Y S} (ny : ∃ y, M.mem y Y)
    (d : (smdl_structure_l I (R := S) ny).Domain) (h : Rf_small_d I Y S d.val) :
    ∃ μ e : (smdl_structure_l I (R := S) ny).Domain,
      Formula.satisfies (⟨Fin.cases μ (Fin.cases d (fun _ => e)), fun _ => d⟩ :
        Env (smdl_structure_l I (R := S) ny) 3) (sc_index_m .newest (.bound 1) (.bound 2)) := by
  obtain ⟨_, valid⟩ := h
  change Formula.satisfies (⟨fun _ => d, fun _ => d⟩ : Env (smdl_structure_l I (R := S) ny) 1)
    (sc_small_m .newest) at valid
  simp only [sc_small_m, Formula.satisfies_exists_iff] at valid
  obtain ⟨μ, e, index⟩ := valid
  refine ⟨μ, e, ?_⟩
  simpa [sc_index_m, sc_total0_m, KP.ord0_m, rd_entry0_m, kpair0_m, pair0_m, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval, Definitional.Term.newest,
    Definitional.Term.weaken, Definitional.Term.rename, Definitional.Term.bind,
    Function.comp_def, Env.push, fin_cases, Fin.cases, Fin.induction, Fin.induction.go] using index

/-- 已有编号图给出小性；只调换同一有限赋值的槽位。 -/
theorem Rf_small_d.of_index_l {X R : M.Domain} (nx : ∃ x, M.mem x X)
    (A μ e : (smdl_structure_l I (R := R) nx).Domain)
    (index : Formula.satisfies (⟨Fin.cases μ (Fin.cases A (fun _ => e)), fun _ => A⟩ :
      Env (smdl_structure_l I (R := R) nx) 3) (sc_index_m .newest (.bound 1) (.bound 2))) :
    Rf_small_d I X R A.val := by
  apply (rf_small_native_l I nx A).mpr
  simp only [sc_small_m, Formula.satisfies_exists_iff]
  refine ⟨μ, e, ?_⟩
  simpa [sc_index_m, sc_total0_m, KP.ord0_m, rd_entry0_m, kpair0_m, pair0_m, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isTransitive_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval, Definitional.Term.newest,
    Definitional.Term.weaken, Definitional.Term.rename, Definitional.Term.bind,
    Function.comp_def, Env.push, fin_cases, Fin.cases, Fin.induction, Fin.induction.go] using index

/-- 完整初等图直接保持小性，目标可以是未坍塌的关系模型。 -/
theorem Smap_d.small_l (hZF : M.Models ZF) {ω c d X R Y S j A B : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j) (image : M.PairMember I A B j) :
    Rf_small_d I X R A ↔ Rf_small_d I Y S B := by
  let a : (smdl_structure_l I (R := R) mx.2.1).Domain := ⟨A, map.1.1.input_mem_of_pairMember image⟩
  let b : (smdl_structure_l I (R := S) my.2.1).Domain := ⟨B, map.1.1.output_mem_of_pairMember image⟩
  exact (rf_small_native_l I mx.2.1 a).trans
    ((smap_source_l I hZF hω mx my map (sc_small_m .newest) (by simp -implicitDefEqProofs)
      ⟨fun _ => a, fun _ => a⟩ ⟨fun _ => b, fun _ => b⟩ (fun _ => image)).trans
        (rf_small_native_l I my.2.1 b).symm)

def rf_small_m {d} (X R A : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := 𝒞) (sc_small_m .newest) X R (fun _ : Fin 1 => A)

@[simp] theorem rf_small_closed_l {d} (X R A : Term d)
    (hx : X.freeSupport = []) (hr : R.freeSupport = []) (ha : A.freeSupport = []) :
    (rf_small_m (𝒞 := 𝒞) X R A).FreeClosed :=
  rr_truth_closed_l _ (by simp -implicitDefEqProofs) X R _ hx hr (fun _ => ha)

theorem rf_small_sat_l {d} (ρ : Env M d) (X R A : Term d) :
    Formula.satisfies ρ (rf_small_m (𝒞 := 𝒞) X R A) ↔
      Rf_small_d I (X.eval ρ) (R.eval ρ) (A.eval ρ) := by
  rw [rf_small_m, rr_truth_sat_l I ρ _ (by simp -implicitDefEqProofs)]
  exact ⟨fun ⟨h, valid⟩ => ⟨h 0, valid⟩, fun ⟨h, valid⟩ => ⟨fun _ => h, valid⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系中的小定义域统一化

小性由原模型中的序数编号公式给出，子集、函数和全部见证也按同一关系读取。
程序仍量化背景中的全部内部代码。实际隶属实例中的字面运算由下述等价式读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sc_uniform_d (ω X R D : M.Domain) : Prop :=
  ∀ nx : ∃ x, M.mem x X, ∀ E F n r i j f A,
    M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
    M.mem i ω → M.mem j ω → i ≠ j → M.mem f E → ∀ hA : M.mem A X,
    (∀ x, M.mem x X → M.PairMember I x A R → M.PairMember I x D R) →
    (∀ x, M.mem x X → M.PairMember I x A R → ∃ y, M.mem y X ∧ Sbin_d I X R E F n r i j f x y) →
      ∃ B C : (smdl_structure_l I (R := R) nx).Domain, Fn0_d (⟨A, hA⟩ : (smdl_structure_l I (R := R) nx).Domain) C B ∧
        ∀ x y : (smdl_structure_l I (R := R) nx).Domain,
          Rd_entry_d x y B → Sbin_d I X R E F n r i j f x.val y.val

def Sc_collection_d (ω X R : M.Domain) : Prop :=
  ∀ nx : ∃ x, M.mem x X, ∀ D μ e : (smdl_structure_l I (R := R) nx).Domain,
    Formula.satisfies (⟨Fin.cases μ (Fin.cases D (fun _ => e)), fun _ => D⟩ : Env (smdl_structure_l I (R := R) nx) 3)
      (sc_index_m .newest (.bound 1) (.bound 2)) → Sc_uniform_d I ω X R D.val

/-- 已实现的小性证书直接启动全部内部程序的统一化。 -/
theorem Sc_collection_d.uniform_l {ω X R D : M.Domain} (h : Sc_collection_d I ω X R)
    (small : Rf_small_d I X R D) : Sc_uniform_d I ω X R D := by
  let nx : ∃ x, M.mem x X := ⟨D, small.mem_l⟩
  let d : (smdl_structure_l I (R := R) nx).Domain := ⟨D, small.mem_l⟩
  obtain ⟨μ, e, index⟩ := small.index_l I nx d
  exact h nx d μ e index

/-- 见证函数仍由原证书提供；这里只在实际隶属码中逐项读回。 -/
theorem sc_uniform_mem_l (h : Extensional M) {ω c X R D : M.Domain}
    (ht : M.TransitiveSet X) (hm : Smem_d I c X R) (hD : M.mem D X) :
    Sc_uniform_d I ω X R D ↔ ∀ E F n r i j f A,
      M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
      M.mem i ω → M.mem j ω → i ≠ j → M.mem f E → M.mem A X → M.MemberSubset A D →
      Scollect_d I X R E F n r i j f A X →
        ∃ B C, M.mem B X ∧ M.mem C X ∧ Suniform_d I X R E F n r i j f A C B := by
  let N := smdl_structure_l I (R := R) hm.1.2.1
  have en := smem_ext_l I hm.1 hm.2 ht h
  have fn (A C B : N.Domain) : Fn0_d A C B ↔ Fn0_d A.val C.val B.val := by
    let ρ : Env N 3 := ⟨Fin.cases A (Fin.cases C (fun _ => B)), fun _ => B⟩
    exact (fn0_sat_l en ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((smem_delta_image_l I hm ht (fn0_delta_l ..) ρ).trans (fn0_sat_l h ..))
  have entry (x y B : N.Domain) : Rd_entry_d x y B ↔ Rd_entry_d x.val y.val B.val := by
    let ρ : Env N 3 := ⟨Fin.cases x (Fin.cases y (fun _ => B)), fun _ => B⟩
    exact (rd_entry0_sat_l en ρ .newest (.bound 1) (.bound 2)).symm.trans
      ((smem_delta_image_l I hm ht (rd_entry0_delta_l ..) ρ).trans (rd_entry0_sat_l h ..))
  constructor
  · intro u E F n r i j f A hE hF hr hi hj hij hf hA sub total
    obtain ⟨B, C, fb, select⟩ := u hm.1.2.1 E F n r i j f A hE hF hr hi hj hij hf hA
      (fun x hx ha => (hm.2 x D).mpr ⟨hx, hD, sub x ((hm.2 x A).mp ha).2.2⟩)
      (fun x _ ha => total x ((hm.2 x A).mp ha).2.2)
    have fb := (fn ⟨A, hA⟩ C B).mp fb
    refine ⟨B.val, C.val, B.property, C.property, fb, fun x y hxy => ?_⟩
    let x₀ : N.Domain := ⟨x, ht A hA x (fb.bound_l hxy).1⟩
    let y₀ : N.Domain := ⟨y, ht C.val C.property y (fb.bound_l hxy).2⟩
    exact select x₀ y₀ ((entry x₀ y₀ B).mpr hxy)
  · intro u nx E F n r i j f A hE hF hr hi hj hij hf hA sub total
    have member x (hx : M.mem x A) := (hm.2 x A).mpr ⟨ht A hA x hx, hA, hx⟩
    obtain ⟨B, C, hB, hC, fb, select⟩ := u E F n r i j f A hE hF hr hi hj hij hf hA
      (fun x hx => ((hm.2 x D).mp (sub x (ht A hA x hx) (member x hx))).2.2)
      (fun x hx => total x (ht A hA x hx) (member x hx))
    exact ⟨⟨B, hB⟩, ⟨C, hC⟩, (fn ⟨A, hA⟩ ⟨C, hC⟩ ⟨B, hB⟩).mpr fb,
      fun x y hxy => select x.val y.val ((entry x y ⟨B, hB⟩).mp hxy)⟩

/-- 原关系编号与字面小性在实际隶属实例中相同；不要求源模型满足 KP。 -/
theorem sc_collection_mem_l (hKP : M.Models KP) {ω c X R : M.Domain}
    (ht : M.TransitiveSet X) (hm : Smem_d I c X R) :
    Sc_collection_d I ω X R ↔ ∀ D, M.mem D X → Sc_small_d X D → Sc_uniform_d I ω X R D := by
  constructor
  · intro h D hD ⟨μ, e, hμ, he, idx⟩
    let ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) 3 :=
      ⟨Fin.cases ⟨μ, hμ⟩ (Fin.cases ⟨D, hD⟩ (fun _ => ⟨e, he⟩)), fun _ => ⟨D, hD⟩⟩
    exact h hm.1.2.1 ⟨D, hD⟩ ⟨μ, hμ⟩ ⟨e, he⟩
      ((smem_delta_image_l I hm ht (sc_index_delta_l ..) ρ).mpr ((sc_index_sat_l hKP ..).mpr idx))
  · intro h nx D μ e idx
    let ρ : Env (smdl_structure_l I (R := R) nx) 3 := ⟨Fin.cases μ (Fin.cases D (fun _ => e)), fun _ => D⟩
    exact h D.val D.property ⟨μ.val, e.val, μ.property, e.property,
      (sc_index_sat_l hKP ..).mp ((smem_delta_image_l I hm ht (sc_index_delta_l ..) ρ).mp idx)⟩

end YesMetaZFC.SetTheory.Internal
