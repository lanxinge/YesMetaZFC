import YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace
import YesMetaZFC.SetTheory.Filter.SourceUltrafilter
import YesMetaZFC.Model.SetTheory.ReducedPower.FullElementary
import YesMetaZFC.Model.SetTheory.Source.Cantor
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Relations.CollectCode
import YesMetaZFC.Model.SetTheory.ReducedPower.Copy
import YesMetaZFC.Model.SetTheory.ReducedPower.Restriction
import YesMetaZFC.SetTheory.Descriptive.Tree.TreeWellFounded
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed

/-! # 相对于源模型的有限支撑测度族

只要求测度决定源中的子集，协调律也只作用于这些子集。完整背景测度
给出原有实例；同一有限幂上的子集一致性将整张测度图转用到另一模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

structure Em_source_d (ω κ L X F : M.Domain) : Prop where
  total : ∀ n a, M.mem n ω → Fn0_d n L a → ∃ U, Rd_entry_d a U F
  function : ∀ a U V, Rd_entry_d a U F → Rd_entry_d a V F → U = V
  measure : ∀ a U, Rd_entry_d a U F → ∃ n D, M.mem n ω ∧ Fn0_d n L a ∧
    Ep_space_d κ n D ∧ Sf_ultra_d X D U

/-- 原测度族的相对公式，保留全部有限支撑而只要求源中的子集二择。 -/
def em_source_m {d} (ω κ L X F : Term d) : Formula 1 d := set[d] ⟪
  (∀ n a, n ∈ ⌜ω⌝ₛ → ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, a) → ∃ U, ⌜rd_entry0_m⌝ₚ(a, U, ⌜F⌝ₛ)) ∧
  (∀ a U V, ⌜rd_entry0_m⌝ₚ(a, U, ⌜F⌝ₛ) → ⌜rd_entry0_m⌝ₚ(a, V, ⌜F⌝ₛ) → U = V) ∧
  (∀ a U, ⌜rd_entry0_m⌝ₚ(a, U, ⌜F⌝ₛ) → ∃ n D, n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, a) ∧
    ⌜ep_space_m⌝ₚ(⌜κ⌝ₛ, n, D) ∧ ⌜sf_ultra_m⌝ₚ(⌜X⌝ₛ, D, U))⟫
derive_free_closed em_source_m

theorem em_source_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L X F : Term d) :
    Formula.satisfies ρ (em_source_m ω κ L X F) ↔
      Em_source_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) := by
  simp only [em_source_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, fn0_sat_l hE, rd_entry0_sat_l hE,
    ep_space_sat_l hE, sf_ultra_sat_l, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨t, f, m⟩ => ⟨t, f, m⟩, fun h => ⟨h.total, h.function, h.measure⟩⟩

def Ec_source_d (I : kpair_convention_l.Interpretation M) (ω κ L X F : M.Domain) : Prop :=
  ∀ m n q a b U V A, M.mem m ω → M.mem n ω → M.mem A X → Es_reindex_d I κ L F m n q a b U V A

def ec_source_m {d} (ω κ L X F : Term d) : Formula 1 d := set[d] ⟪
  ∀ m n q a b U V A, m ∈ ⌜ω⌝ₛ → n ∈ ⌜ω⌝ₛ → A ∈ ⌜X⌝ₛ →
    ⌜es_reindex_m (𝒞 := kpair_convention_l)⌝ₚ(⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜F⌝ₛ, m, n, q, a, b, U, V, A)⟫
derive_free_closed ec_source_m

theorem ec_source_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω κ L X F : Term d) :
    Formula.satisfies ρ (ec_source_m ω κ L X F) ↔
      Ec_source_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) := by
  simp only [ec_source_m, Ec_source_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, es_reindex_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

/-- 精确的施加条件：所有内部有限 κ 幂上的源子集一致。 -/
def Ea_agree_d (ω κ X Y : M.Domain) : Prop := ∀ n D A, M.mem n ω → Ep_space_d κ n D →
  M.MemberSubset A D → (M.mem A X ↔ M.mem A Y)

/-- 编码搬运只需一个方向：源的有限幂子集都属于目标。 -/
def Ea_subset_d (ω κ X Y : M.Domain) : Prop := ∀ n D A, M.mem n ω → Ep_space_d κ n D →
  M.MemberSubset A D → M.mem A X → M.mem A Y

theorem Ea_agree_d.subset_l {ω κ X Y : M.Domain} (h : Ea_agree_d ω κ X Y) : Ea_subset_d ω κ X Y :=
  fun n D A hn hd sub => (h n D A hn hd sub).mp

theorem Ea_subset_d.trans_l {ω κ X Y Z : M.Domain} (h : Ea_subset_d ω κ X Y) (k : Ea_subset_d ω κ Y Z) :
    Ea_subset_d ω κ X Z := fun n D A hn hd sub hx => k n D A hn hd sub (h n D A hn hd sub hx)

theorem Ea_subset_d.mono_l (hZF : M.Models ZF) {ω κ μ X Y : M.Domain}
    (h : Ea_subset_d ω κ X Y) (hμ : M.MemberSubset μ κ) : Ea_subset_d ω μ X Y := by
  intro n D A hn hD sub hA
  obtain ⟨E, he⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n κ
  have hE : Ep_space_d κ n E := fun s => (he s).trans
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩
  exact h n E A hn hE (fun s hs => (hE s).mpr (((hD s).mp (sub s hs)).mono_target_l hμ)) hA

/-- 完整字母表上的一致性自动覆盖任意子字母表，包含端点本身。 -/
theorem Ea_agree_d.mono_l (hZF : M.Models ZF) {ω κ μ X Y : M.Domain}
    (h : Ea_agree_d ω κ X Y) (hμ : M.MemberSubset μ κ) : Ea_agree_d ω μ X Y := by
  intro n D A hn hD sub
  obtain ⟨E, he⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) n κ
  have hE : Ep_space_d κ n E := fun s => (he s).trans
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩
  exact h n E A hn hE (fun s hs => (hE s).mpr (((hD s).mp (sub s hs)).mono_target_l hμ))

theorem Em_source_d.at_l (hE : Extensional M) {ω κ L X F a U n D : M.Domain}
    (h : Em_source_d ω κ L X F) (ha : Rd_entry_d a U F) (hn : Fn0_d n L a)
    (hD : Ep_space_d κ n D) : Sf_ultra_d X D U := by
  obtain ⟨m, E, _, hm, he, hu⟩ := h.measure a U ha
  have en := hm.domain_eq_l hE hn
  subst m
  exact hE.eq_of_same_members E D (fun s => (he s).trans (hD s).symm) ▸ hu

theorem Em_family_d.source_l (hKP : M.Models KP) {ω κ L F : M.Domain}
    (powers : ∀ n D, M.mem n ω → Ep_space_d κ n D → ∃ P, M.IsPowerSetOf P D)
    (h : Em_family_d ω κ L F) (X : M.Domain) : Em_source_d ω κ L X F := by
  refine ⟨h.total, h.function, fun a U ha => ?_⟩
  obtain ⟨n, D, hn, hna, hd, hu⟩ := h.measure a U ha
  exact ⟨n, D, hn, hna, hd, hu.source_l hKP (powers n D hn hd) X⟩

theorem Es_coherent_d.source_l (I : kpair_convention_l.Interpretation M) {ω κ L F : M.Domain}
    (h : Es_coherent_d I ω κ L F) (X : M.Domain) : Ec_source_d I ω κ L X F :=
  fun m n q a b U V A hm hn _ => h m n q a b U V A hm hn

theorem Em_source_d.transfer_l {ω κ L X Y F : M.Domain} (h : Em_source_d ω κ L X F)
    (agree : Ea_agree_d ω κ X Y) : Em_source_d ω κ L Y F := by
  refine ⟨h.total, h.function, fun a U ha => ?_⟩
  obtain ⟨n, D, hn, hna, hd, hu⟩ := h.measure a U ha
  exact ⟨n, D, hn, hna, hd, hu.transfer_l (fun A hA => agree n D A hn hd hA)⟩

theorem Ec_source_d.transfer_l (hZF : M.Models ZF) {ω κ L X Y F : M.Domain}
    (h : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F) (agree : Ea_agree_d ω κ X Y) :
    Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L Y F := by
  intro m n q a b U V A hm hn hAY hq ha hb haV hbU hA
  obtain ⟨D, hd⟩ := ZF.exists_functionSpace hZF (kp_pair_l (ZF.modelsKP hZF)) m κ
  have space : Ep_space_d κ m D := fun s => (hd s).trans
    ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩
  exact h m n q a b U V A hm hn ((agree m D A hm space (fun s hs => (space s).mpr (hA s hs))).mpr hAY)
    hq ha hb haV hbU hA

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全部有限支撑源分量的统一模型图

每个分量都以源中的函数族形成规范等价类。规范性给出结构码唯一性，随后
一次替换生成整个模型图；不逐分量选择模型，也不加入外部函数代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ep_component_d (ω κ L X R F a c : M.Domain) : Prop := ∃ n D U G p C T,
  M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Rd_entry_d a U F ∧
  (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧ Rp_model_d I D X U R c G p C T

def ep_component_m {d} (ω κ L X R F a c : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+7) := x.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (.mem (.bound 6) (w ω)) (.conj (fn0_m (.bound 6) (w L) (w a))
      (.conj (ep_space_m (w κ) (.bound 6) (.bound 5)) (.conj (rd_entry_m (w a) (.bound 4) (w F))
        (.conj (.forallE (.iff (.mem .newest (.bound 4)) (.conj (.mem .newest (w X).weaken)
          (fn0_m (.bound 6) (w X).weaken .newest))))
          (rp_model_m (𝒞 := kpair_convention_l) (.bound 5) (w X) (.bound 4) (w R) (w c)
            (.bound 3) (.bound 2) (.bound 1) .newest))))))))))))
derive_free_closed ep_component_m

theorem ep_component_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L X R F a c : Term d) :
    Formula.satisfies ρ (ep_component_m ω κ L X R F a c) ↔
      Ep_component_d I (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (R.eval ρ) (F.eval ρ) (a.eval ρ) (c.eval ρ) := by
  simp only [ep_component_m, Ep_component_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, ep_space_sat_l hE, rd_entry_sat_l hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, rp_model_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem ep_component_pair_l (hE : Extensional M) {ω κ L X R S F a c d : M.Domain}
    (hF : Em_source_d ω κ L X F) (hc : Ep_component_d I ω κ L X R F a c)
    (hd : Ep_component_d I ω κ L X S F a d) : ∃ n D U G p C T V,
      M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧ Rd_entry_d a U F ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧
      Rp_model_d I D X U R c G p C T ∧ Rp_model_d I D X U S d G p C V := by
  obtain ⟨n, D, U, G, p, C, T, hnω, hn, hD, haU, hG, hm⟩ := hc
  obtain ⟨n', D', U', G', p', C', T', _, hn', hD', haU', hG', hm'⟩ := hd
  have e := hn'.domain_eq_l hE hn
  subst n'
  have e := hE.eq_of_same_members D' D (fun s => (hD' s).trans (hD s).symm)
  subst D'
  have e := hF.function a U' U haU' haU
  subst U'
  have e := hE.eq_of_same_members G' G (fun f => (hG' f).trans (hG f).symm)
  subst G'
  have ep := hm'.map.projection.1.1.eq_of_pairMember_iff hE hm.map.projection.1.1
    (fun f B => (hm'.map.classes f B).trans (hm.map.classes f B).symm)
  subst p'
  have ec := hE.eq_of_same_members C' C (fun B => (hm'.map.range B).trans (hm.map.range B).symm)
  subst C'
  exact ⟨n, D, U, G, p, C, T, T', hnω, hn, hD, haU, hG, hm, hm'⟩

theorem ep_component_unique_l (hE : Extensional M) {ω κ L X R F a c d : M.Domain}
    (hF : Em_source_d ω κ L X F) (hc : Ep_component_d I ω κ L X R F a c)
    (hd : Ep_component_d I ω κ L X R F a d) : c = d := by
  obtain ⟨_, D, U, G, p, C, T, T', _, _, _, _, _, hm, hm'⟩ := ep_component_pair_l I hE hF hc hd
  exact hm.unique_l I hE hm'

variable (hZF : M.Models ZF)
local notation "Kp" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_components_l {ω κ K L X R F J : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (hJ : ∀ a, M.mem a J → ∃ n, M.mem n ω ∧ Fn0_d n L a) (S : M.Domain) : ∃ Z Q, Fn0_d J Q Z ∧
      ∀ a c, Rd_entry_d a c Z → Ep_component_d Kp ω κ L X S F a c := by
  let ρ := (((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push κ).push L).push X).push S).push F
  let φ : BinarySchema 6 := {
    body := ep_component_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat a c : φ.denote ρ a c ↔ Ep_component_d Kp ω κ L X S F a c := ep_component_sat_l Kp hZF.1 _ _ _ _ _ _ _ _ _
  have total a (ha : M.mem a J) : ∃ c, φ.denote ρ a c := by
    obtain ⟨n, hn, hna⟩ := hJ a ha
    obtain ⟨U, haU⟩ := hF.total n a hn hna
    obtain ⟨n', D, _, hna', hD, hU⟩ := hF.measure a U haU
    have en := hna'.domain_eq_l hZF.1 hna
    subst n'
    obtain ⟨G, c, p, C, T, hG, hm⟩ := h.model_l hZF hn hD hU.base S
    exact ⟨c, (sat a c).mpr ⟨n, D, U, G, p, C, T, hn, hna, hD, haU, hG, hm⟩⟩
  have unique a (_ : M.mem a J) c d hc hd := ep_component_unique_l Kp hZF.1 hF ((sat a c).mp hc) ((sat a d).mp hd)
  obtain ⟨Q, hQ⟩ := ZF.exists_functionalImageOn hZF φ ρ J total unique
  obtain ⟨Z, hz, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF Kp φ ρ total unique
    (fun a c ha hc => (hQ c).mpr ⟨a, ha, hc⟩)
  exact ⟨Z, Q, fn0_of_function_l (ZF.modelsKP hZF) hz, fun a c hc => (sat a c).mp ((spec a c).mp hc).2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 全系统过渡映射的统一图公式

类之间的箭头以类中代表的坐标拉回表达。任意代表都能实现同一箭头；因此
后续恒等、复合证明不必为不同分量选择一致的代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Ep_arrow_d (ω κ L X a b B C : M.Domain) : Prop := ∃ m n q f g,
  M.mem m ω ∧ M.mem n ω ∧ Fn0_d m n q ∧ Fn0_d n L b ∧ Cp0_d m n L q b a ∧
  M.mem f B ∧ M.mem g C ∧ Ep_pull_d κ X m n q f g

def ep_arrow_m {d} (ω κ L X a b B C : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+5) := x.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 4) (w ω))
    (.conj (.mem (.bound 3) (w ω)) (.conj (fn0_m (.bound 4) (.bound 3) (.bound 2))
      (.conj (fn0_m (.bound 3) (w L) (w b)) (.conj (cp0_m (.bound 4) (.bound 3) (w L) (.bound 2) (w b) (w a))
        (.conj (.mem (.bound 1) (w B)) (.conj (.mem .newest (w C))
          (ep_pull_m (w κ) (w X) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))))))))
derive_free_closed ep_arrow_m

theorem ep_arrow_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L X a b B C : Term d) :
    Formula.satisfies ρ (ep_arrow_m ω κ L X a b B C) ↔
      Ep_arrow_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (a.eval ρ) (b.eval ρ) (B.eval ρ) (C.eval ρ) := by
  simp only [ep_arrow_m, Ep_arrow_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, cp0_sat_l hE, ep_pull_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ep_map_l (hZF : M.Models ZF) {ω κ K L X R F a b c d m n q : M.Domain}
    (h : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hF : Em_source_d ω κ L X F)
    (hco : Ec_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X F)
    (hm : M.mem m ω) (hn : M.mem n ω) (hq : Fn0_d m n q) (hb : Fn0_d n L b)
    (hinj : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j) (hqa : Cp0_d m n L q b a)
    (haM : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a c)
    (hbM : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F b d) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ j C S E T, Smdl_d I c C S ∧ Smdl_d I d E T ∧ M.IsSetInjectionFromTo I j C E ∧
      Smap_d I ω c d C E j ∧
      (∀ B D B' D', Rd_entry_d B B' j → Rd_entry_d D D' j → (Rd_entry_d B D S ↔ Rd_entry_d B' D' T)) ∧
      (∀ B D, Rd_entry_d B D j ↔ M.mem B C ∧ M.mem D E ∧ Ep_arrow_d ω κ L X a b B D) ∧
      ∀ B D, Rd_entry_d B D j → ∀ f, M.mem f B → ∃ g, M.mem g D ∧ Ep_pull_d κ X m n q f g := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨m', D₀, U, G₀, p₀, C, S, _, ha, hD₀, haU, hG₀, hM₀⟩ := haM
  obtain ⟨n', D₁, V, G₁, p₁, E, T, _, hb', hD₁, hbV, hG₁, hM₁⟩ := hbM
  have em := ha.domain_eq_l hZF.1 hqa.1
  subst m'
  have en := hb'.domain_eq_l hZF.1 hb
  subst n'
  have hU := hF.at_l hZF.1 haU ha hD₀
  have hV := hF.at_l hZF.1 hbV hb hD₁
  obtain ⟨t, P, htX, ht, ts, hp, ps⟩ := h.family_l hZF hm hn hq hD₀ hD₁ hG₀ hG₁
  obtain ⟨c₀, hm₀⟩ := h.code
  obtain ⟨Q₀, U', hQ₀, hu, us, model₀⟩ := rs_restrict_model_l hZF h.omega h.transitive hm₀ h.theory
    (h.space_mem_l hZF hm hD₀) hU hG₀ hM₀
  obtain ⟨Q₁, V', hQ₁, hv, vs, model₁⟩ := rs_restrict_model_l hZF h.omega h.transitive hm₀ h.theory
    (h.space_mem_l hZF hn hD₁) hV hG₁ hM₁
  have push : Push_d D₀ D₁ Q₀ Q₁ U' V' t := ⟨ht, fun A hA => by
    obtain ⟨B, hBX, bs⟩ := sc_pull_l I hZF h.omega h.transitive hm₀ h.theory
      (h.space_mem_l hZF hn hD₁) htX ((hQ₀ A).mp hA).1
    have hBQ := (hQ₁ B).mpr ⟨hBX, fun s hs => ((bs s).mp hs).1⟩
    obtain ⟨B', hB', eq⟩ := hco m n q b a U V A hm hn ((hQ₀ A).mp hA).1 hq hb hqa hbV haU
      (fun r hr => (hD₀ r).mp (((hQ₀ A).mp hA).2 r hr))
    have eB : B' = B := hZF.1.eq_of_same_members B' B fun s => (hB' s).trans
      ⟨fun ⟨hs, r, hr, hsr⟩ => (bs s).mpr ⟨(hD₁ s).mpr hs, r, hr, (ts s r).mpr ⟨(hD₁ s).mpr hs, hsr⟩⟩,
        fun hs => by
          obtain ⟨hs, r, hr, hsr⟩ := (bs s).mp hs
          exact ⟨(hD₁ s).mp hs, r, hr, ((ts s r).mp hsr).2⟩⟩
    subst B'
    have vr : M.mem B V' ↔ M.mem B V := (vs B).trans ⟨And.right, fun h => ⟨hBQ, h⟩⟩
    have ur : M.mem A U' ↔ M.mem A U := (us A).trans ⟨And.right, fun h => ⟨hA, h⟩⟩
    exact ⟨B, hBQ, bs, vr.trans (eq.trans ur.symm)⟩⟩
  obtain ⟨P', j, hp', ps', elem, lift⟩ := rs_projection_embedding_l hZF h.omega h.transitive hm₀ h.theory
    (h.uniform_l hZF hm hD₀) (h.uniform_l hZF hn hD₁) (h.space_mem_l hZF hm hD₀) (h.space_mem_l hZF hn hD₁) htX hQ₀ hQ₁ hu hv push hG₀ hG₁ model₀ model₁
  have eqP := hp'.1.1.eq_of_pairMember_iff hZF.1 hp.1.1 (fun f g => (ps' f g).trans (ps f g).symm)
  subst P'
  have hj := elem.1
  have rel B D B' D' (hb : Rd_entry_d B B' j) (hd : Rd_entry_d D D' j) :=
    elem.relation_l I hZF h.omega hM₀.code hM₁.code hb hd
  have pull f g (hfg : Rd_entry_d f g P) : Ep_pull_d κ X m n q f g :=
    ep_pull_of_comp_l hD₀ hD₁ ht (hM₀.map.functions f (hp.input_mem_of_pairMember hfg)) ts ((ps f g).mp hfg).2.2
  have any B D (hBD : Rd_entry_d B D j) f (hf : M.mem f B) : ∃ g, M.mem g D ∧ Ep_pull_d κ X m n q f g := by
    have hfp := hM₀.map.member_l I hZF.1 hU.base (hj.1.input_mem_of_pairMember hBD) hf
    obtain ⟨g, hg, hfg⟩ := hp.2.2 f (hM₀.map.projection.input_mem_of_pairMember hfp)
    obtain ⟨D', _, hgp⟩ := hM₁.map.projection.2.2 g hg
    have e := hj.1.1.2 B D' D (lift f g B D' hfg hfp hgp) hBD
    exact ⟨g, e ▸ hM₁.map.representative_l I hV.base hgp, pull f g hfg⟩
  refine ⟨j, C, S, E, T, hM₀.code, hM₁.code, hj, elem, rel, fun B D => ⟨?_, ?_⟩, any⟩
  · intro hBD
    have hBC := hj.1.input_mem_of_pairMember hBD
    obtain ⟨f, hf⟩ := (hM₀.map.range B).mp hBC
    have hff := hM₀.map.representative_l I hU.base hf
    obtain ⟨g, hg, hfg⟩ := any B D hBD f hff
    exact ⟨hBC, hj.1.output_mem_of_pairMember hBD, m, n, q, f, g, hm, hn, hq, hb, hqa, hff, hg, hfg⟩
  · rintro ⟨hBC, hDE, m', n', q', f, g, _, _, hq', hb', hqa', hfB, hgD, hfg⟩
    have en := hb'.domain_eq_l hZF.1 hb
    subst n'
    have em := hqa'.1.domain_eq_l hZF.1 ha
    subst m'
    have eq := ec_factor_unique_l hZF.1 hinj hq' hq hqa' hqa
    subst q'
    have hfp := hM₀.map.member_l I hZF.1 hU.base hBC hfB
    have hgp := hM₁.map.member_l I hZF.1 hV.base hDE hgD
    obtain ⟨g', _, hfg'⟩ := hp.2.2 f (hM₀.map.projection.input_mem_of_pairMember hfp)
    have eg := ep_pull_unique_l (ZF.modelsKP hZF) hq (pull f g' hfg') hfg
    exact lift f g B D (eg ▸ hfg') hfp hgp

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限幂一致性搬运小关系及其传递塌缩

二元关系先编码为二项 κ 值列的集合。搬运此集合后，在目标源内逐项还原
Kuratowski 有序对，并分离出原关系。目标的实际塌缩闭包和唯一性随后还原
同一个传递集合；这正是小模型的关系编码跨源搬运所需的步骤。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

include hZF in
/-- 两个不同坐标可指定任意值，其余坐标取第二个值；只用实际 ZF 函数构造。 -/
theorem ep_two_values_l {κ n z o a b : M.Domain} (hne : z ≠ o)
    (hz : M.mem z n) (ho : M.mem o n) (ha : M.mem a κ) (hb : M.mem b κ) :
    ∃ s, Fn0_d n κ s ∧ Rd_entry_d z a s ∧ Rd_entry_d o b s := by
  classical
  let ρ : Env M 3 := ⟨Fin.cases z (Fin.cases a (fun _ => b)), fun _ => z⟩
  let φ : BinarySchema 3 := {
    body := .disj
      (.conj (Formula.extensionalEq (.bound 1) (.bound 2)) (Formula.extensionalEq .newest (.bound 3)))
      (.conj (.neg (Formula.extensionalEq (.bound 1) (.bound 2))) (Formula.extensionalEq .newest (.bound 4))) }
  have sat i x : φ.denote ρ i x ↔ (i = z ∧ x = a) ∨ (i ≠ z ∧ x = b) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨s, hs, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := κ)
    (fun i _ => by
      by_cases hi : i = z
      · exact ⟨a, (sat i a).mpr (Or.inl ⟨hi, rfl⟩)⟩
      · exact ⟨b, (sat i b).mpr (Or.inr ⟨hi, rfl⟩)⟩)
    (fun i _ x y hx hy => by
      rcases (sat i x).mp hx with ⟨hi, rfl⟩ | ⟨hi, rfl⟩ <;>
        rcases (sat i y).mp hy with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
      · rfl
      · exact (hj hi).elim
      · exact (hi hj).elim
      · rfl)
    (fun i x _ hx => ((sat i x).mp hx).elim (fun h => h.2.symm ▸ ha) (fun h => h.2.symm ▸ hb))
  exact ⟨s, fn0_of_function_l (ZF.modelsKP hZF) hs,
    (spec z a).mpr ⟨hz, (sat z a).mpr (Or.inl ⟨rfl, rfl⟩)⟩,
    (spec o b).mpr ⟨ho, (sat o b).mpr (Or.inr ⟨Ne.symm hne, rfl⟩)⟩⟩

def ep_binary_pair_m {d} (κ z o s p : Term d) : Formula 1 d :=
  Formula.existsMem κ (Formula.existsMem κ.weaken
    (.conj (rd_entry0_m z.weaken.weaken (.bound 1) s.weaken.weaken)
      (.conj (rd_entry0_m o.weaken.weaken .newest s.weaken.weaken)
        (kpair0_m p.weaken.weaken (.bound 1) .newest))))
derive_free_closed ep_binary_pair_m

theorem ep_binary_pair_delta_l {d} (κ z o s p : Term d) : (ep_binary_pair_m κ z o s p).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (kpair0_delta_l ..))))

theorem ep_binary_pair_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ z o s p : Term d) :
    Formula.satisfies ρ (ep_binary_pair_m κ z o s p) ↔
      ∃ a, M.mem a (κ.eval ρ) ∧ ∃ b, M.mem b (κ.eval ρ) ∧
        Rd_entry_d (z.eval ρ) a (s.eval ρ) ∧ Rd_entry_d (o.eval ρ) b (s.eval ρ) ∧ KPair_d M (p.eval ρ) a b := by
  simp only [ep_binary_pair_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, kpair0_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 源内基本配对给出任意两个已知对象的 Kuratowski 对。 -/
theorem Ep_source_d.kpair_l {ω κ K X R a b : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (ha : M.mem a X) (hb : M.mem b X) : ∃ p, M.mem p X ∧ KPair_d M p a b :=
  (source.algebra_l (ZF.modelsKP hZF)).kpair_l ha hb

/-- 源的实际乘积闭包直接给出任意字母表的平方。 -/
theorem Ep_source_d.square_l {ω κ K X R A : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hA : M.mem A X) : ∃ P, M.mem P X ∧ M.IsCartesianProduct I P A A :=
  (source.algebra_l (ZF.modelsKP hZF)).product A A hA hA

/-- 任意源内二元关系在 κ 上的部分，编码为一个实际有限 κ 幂子集。 -/
theorem ep_relation_code_l {ω κ K X R T : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hT : M.mem T X) :
    ∃ n z o D C, M.mem n ω ∧ M.mem z ω ∧ M.mem o ω ∧ Ep_space_d κ n D ∧ M.mem C X ∧ M.MemberSubset C D ∧
      ∀ a b, M.mem a κ → M.mem b κ → (Rd_entry_d a b T ↔ ∃ s, M.mem s C ∧ Rd_entry_d z a s ∧ Rd_entry_d o b s) := by
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨o, ho, hoω⟩ := source.omega.1.2 z hzω
  obtain ⟨n, hn, hnω⟩ := source.omega.1.2 o hoω
  have hzo : z ≠ o := by intro e; subst o; exact hz z ho.predecessor_mem
  have hzn := (hn z).mpr (Or.inl ho.predecessor_mem)
  obtain ⟨D, hDX, hD⟩ := source.space_l hZF hnω
  obtain ⟨c, hc⟩ := source.code
  let ρ : Env M 4 := ⟨Fin.cases z (Fin.cases o (Fin.cases κ (fun _ => T))), fun _ => z⟩
  let φ : UnarySchema 4 := { body := Formula.existsMem (.bound 3) (Formula.existsMem (.bound 4)
    (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 2))
      (.conj (rd_entry0_m (.bound 4) .newest (.bound 2)) (rd_entry0_m (.bound 1) .newest (.bound 6))))) }
  have sat s : φ.denote ρ s ↔ ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧
      Rd_entry_d z a s ∧ Rd_entry_d o b s ∧ Rd_entry_d a b T := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨C, hCX, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))
    ρ (Fin.cases (source.transitive ω source.omega_mem z hzω)
      (Fin.cases (source.transitive ω source.omega_mem o hoω) (Fin.cases source.cardinal_mem (fun _ => hT)))) hDX
  have code s : M.mem s C ↔ M.mem s D ∧ ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧
      Rd_entry_d z a s ∧ Rd_entry_d o b s ∧ Rd_entry_d a b T := (spec s).trans (and_congr_right fun _ => sat s)
  refine ⟨n, z, o, D, C, hnω, hzω, hoω, hD, hCX, fun s hs => ((code s).mp hs).1, fun a b ha hb => ⟨?_, ?_⟩⟩
  · intro hab
    obtain ⟨s, hs, hza, hob⟩ := ep_two_values_l hZF hzo hzn hn.predecessor_mem ha hb
    exact ⟨s, (code s).mpr ⟨(hD s).mpr hs, a, ha, b, hb, hza, hob, hab⟩, hza, hob⟩
  · rintro ⟨s, hs, hza, hob⟩
    obtain ⟨hsD, a', _, b', _, hza', hob', hab⟩ := (code s).mp hs
    have fn := fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hsD)
    exact fn.1.2 z a' a hza' hza ▸ fn.1.2 o b' b hob' hob ▸ hab

/-- 有限幂子集的单向包含搬运源中的实际二元关系。 -/
theorem Ea_subset_d.relation_l {ω κ K X R K' Y S T : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (hT : M.mem T X)
    (bound : ∀ p, M.mem p T → ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧ KPair_d M p a b) : M.mem T Y := by
  obtain ⟨n, z, o, D, C, hnω, hzω, hoω, hD, hCX, sub, code⟩ := ep_relation_code_l hZF source hT
  have hCY := subsets n D C hnω hD sub hCX
  obtain ⟨d, hd⟩ := target.code
  have hzY := target.transitive ω target.omega_mem z hzω
  have hoY := target.transitive ω target.omega_mem o hoω
  let η : Env M 3 := ⟨Fin.cases z (Fin.cases o (fun _ => κ)), fun _ => z⟩
  let ψ : BinarySchema 3 := { body := ep_binary_pair_m (.bound 4) (.bound 2) (.bound 3) (.bound 1) .newest }
  have read s p : ψ.denote η s p ↔ ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧
      Rd_entry_d z a s ∧ Rd_entry_d o b s ∧ KPair_d M p a b := ep_binary_pair_sat_l hZF.1 ..
  obtain ⟨B, hBY, product⟩ := (target.algebra_l (ZF.modelsKP hZF)).product κ κ target.cardinal_mem target.cardinal_mem
  let ξ : Env M 4 := ⟨Fin.cases z (Fin.cases o (Fin.cases κ (fun _ => C))), fun _ => z⟩
  let χ : UnarySchema 4 := {
    body := Formula.existsMem (.bound 4)
      (ep_binary_pair_m (.bound 4) (.bound 2) (.bound 3) .newest (.bound 1)) }
  have decoded p : χ.denote ξ p ↔ ∃ s, M.mem s C ∧ ψ.denote η s p := by
    simp only [χ, UnarySchema.denote, Formula.satisfies_existsMem_iff, ep_binary_pair_sat_l hZF.1]
    exact exists_congr fun s => and_congr_right fun _ => (read s p).symm
  obtain ⟨Q, hQY, qs⟩ := sc_separate_source_l I hZF target.omega target.transitive hd target.theory
    χ (.existsMem _ (ep_binary_pair_delta_l ..)) ξ
    (Fin.cases hzY (Fin.cases hoY (Fin.cases target.cardinal_mem (fun _ => hCY)))) hBY
  have eq : Q = T := hZF.1.eq_of_same_members Q T (fun p => by
    rw [qs p, decoded p]
    constructor
    · rintro ⟨_, s, hs, hp⟩
      obtain ⟨a, ha, b, hb, hza, hob, hp⟩ := (read s p).mp hp
      obtain ⟨q, hq, hqT⟩ := (code a b ha hb).mpr ⟨s, hs, hza, hob⟩
      exact (kpair_unique_l M hZF.1 hq hp) ▸ hqT
    · intro hpT
      obtain ⟨a, ha, b, hb, hp⟩ := bound p hpT
      obtain ⟨s, hsC, hza, hob⟩ := (code a b ha hb).mp ⟨p, hp, hpT⟩
      exact ⟨(product p).mpr ⟨a, ha, b, hb, hp⟩, s, hsC, (read s p).mpr ⟨a, ha, b, hb, hza, hob, hp⟩⟩)
  exact eq ▸ hQY

/-- 搬运小关系码并在目标源内重新塌缩，得到同一个实际传递集合。 -/
theorem Ea_subset_d.collapse_l {ω κ K X R K' Y S A T B F : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (hA : M.mem A Y) (small : Sc_small_d Y A) (hT : M.mem T X)
    (bound : ∀ p, M.mem p T → ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧ KPair_d M p a b)
    (h : Wc_iso_d A T B F) : M.mem B Y ∧ M.mem F Y := by
  obtain ⟨c, model⟩ := target.code
  obtain ⟨C, G, hC, hG, g⟩ := target.collapse.collapse_l I (ZF.modelsKP hZF) target.transitive model hA
    (subsets.relation_l hZF source target hT bound) small (h.well_founded_l (ZF.modelsKP hZF)) (h.extensional_l hZF.1)
  exact ⟨(h.unique_l hZF g).symm ▸ hC, (h.graph_unique_l hZF g).symm ▸ hG⟩

/-- 诱导隶属关系由源内平方中的有界分离得到，无须另假设关系码属于源。 -/
theorem Ep_source_d.membership_relation_l {ω κ K Z W c A R : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z W) (hA : M.mem A Z) (hm : Smem_d I c A R) : M.mem R Z := by
  obtain ⟨P, hPZ, hP⟩ := source.square_l hZF hA
  obtain ⟨c₀, hc⟩ := source.code
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  let φ : UnarySchema 1 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (.mem (.bound 1) .newest))) }
  have sat p : φ.denote ρ p ↔ ∃ x, M.mem x A ∧ ∃ y, M.mem y A ∧ KPair_d M p x y ∧ M.mem x y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨Q, hQZ, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.mem _ _)))) ρ (fun _ => hA) hPZ
  have eq : Q = R := hZF.1.eq_of_same_members Q R (fun p => ⟨fun hp => by
    obtain ⟨x, hx, y, hy, hpair, hxy⟩ := (sat p).mp ((spec p).mp hp).2
    obtain ⟨q, hq, hqR⟩ := (hm.2 x y).mpr ⟨hx, hy, hxy⟩
    exact kpair_unique_l M hZF.1 hq hpair ▸ hqR, fun hp => by
    obtain ⟨x, y, hpair⟩ := hm.1.2.2.1 p hp
    obtain ⟨hx, hy, hxy⟩ := (hm.2 x y).mp ⟨p, hpair, hp⟩
    exact (spec p).mpr ⟨(hP p).mpr ⟨x, hx, y, hy, hpair⟩, (sat p).mpr ⟨x, hx, y, hy, hpair, hxy⟩⟩⟩)
  exact eq ▸ hQZ

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从实际小枚举自动编码并搬运传递模型

给定源内的任意 A→B 双射图，把 B 的隶属关系拉回 A×A，再在源中实际分离
关系码。A=κ 时，有限幂一致性将此码送到另一源；在那里计算 Mostowski 塌缩，
唯一性识别出原来的 B。调用者只提供实际枚举，无需另给关系码或良基证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_transitive_code_l {ω κ K X R A B F : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hB : M.TransitiveSet B) (hF : M.mem F X) (bij : M.IsSetBijectionFromTo I F A B) :
    ∃ T, M.mem T X ∧
      (∀ p, M.mem p T → ∃ a, M.mem a A ∧ ∃ b, M.mem b A ∧ KPair_d M p a b) ∧ Wc_iso_d A T B F := by
  have hf := fn0_of_function_l (ZF.modelsKP hZF) bij.1.1
  obtain ⟨_, C, hCX, hfc⟩ := source.function_l hZF hF
    (hf.retarget_l fun a b hab => (rd_entry_transitive_l source.transitive hF hab).2)
  obtain ⟨c, hc⟩ := source.code
  have hAX := sc_function_domain_mem_l hZF source.omega source.transitive hc source.theory hF hf
  obtain ⟨P, hPX, hP⟩ := source.square_l hZF hAX
  let ρ : Env M 3 := ⟨Fin.cases A (Fin.cases C (fun _ => F)), fun _ => A⟩
  let φ : UnarySchema 3 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (Formula.existsMem (.bound 4) (Formula.existsMem (.bound 5)
        (.conj (kpair0_m (.bound 4) (.bound 3) (.bound 2))
          (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 7))
            (.conj (rd_entry0_m (.bound 2) .newest (.bound 7)) (.mem (.bound 1) .newest))))))) }
  have sat p : φ.denote ρ p ↔ ∃ a, M.mem a A ∧ ∃ b, M.mem b A ∧ ∃ x, M.mem x C ∧ ∃ y, M.mem y C ∧
      KPair_d M p a b ∧ Rd_entry_d a x F ∧ Rd_entry_d b y F ∧ M.mem x y := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1, Formula.satisfies_mem_iff]; rfl
  obtain ⟨T, hTX, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.mem _ _))))))))
    ρ (Fin.cases hAX (Fin.cases hCX (fun _ => hF))) hPX
  refine ⟨T, hTX, fun p hp => (hP p).mp ((spec p).mp hp).1,
    ⟨hB, hf, bij.2, fun a _ b _ x _ => bij.1.2 a b x, ?_⟩⟩
  intro a ha b hb x hx y hy hax hby
  constructor
  · rintro ⟨p, hp, hpT⟩
    obtain ⟨a', _, b', _, v, _, w, _, hq, hav, hbw, hvw⟩ := (sat p).mp ((spec p).mp hpT).2
    obtain ⟨ea, eb⟩ := kpair_injective_l M hq hp
    exact bij.1.1.1.2 a v x (ea ▸ hav) hax ▸ bij.1.1.1.2 b w y (eb ▸ hbw) hby ▸ hvw
  · intro hxy
    obtain ⟨p, _, hp⟩ := source.kpair_l hZF (source.transitive A hAX a ha) (source.transitive A hAX b hb)
    exact ⟨p, hp, (spec p).mpr ⟨(hP p).mpr ⟨a, ha, b, hb, hp⟩,
      (sat p).mpr ⟨a, ha, b, hb, x, (hfc.bound_l hax).2, y, (hfc.bound_l hby).2, hp, hax, hby, hxy⟩⟩⟩

/-- 小传递模型的跨源还原：关系码、目标内塌缩及其与 B 的相等均自动证明。 -/
theorem Ea_subset_d.transitive_l {ω κ K X R K' Y S B F : M.Domain}
    (subsets : Ea_subset_d ω κ X Y) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S) (hB : M.TransitiveSet B)
    (hF : M.mem F X) (bij : M.IsSetBijectionFromTo I F κ B) : M.mem B Y := by
  obtain ⟨T, hT, bound, iso⟩ := ep_transitive_code_l hZF source hB hF bij
  exact (subsets.collapse_l hZF source target target.cardinal_mem (target.cardinal_small_l (ZF.modelsKP hZF)) hT bound iso).1

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源内乘积沿有限列编号

把两个坐标的已有编号放在同一有限列的零、一位置，再用源内有限列编号。
全过程产生实际源内单射；字母表只要求是包含 ω 的序数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_product_index_l {ω κ K X R A B D f g : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hA : M.mem A X) (hB : M.mem B X) (hD : M.mem D X)
    (product : M.IsCartesianProduct I D A B) (hf : M.mem f X) (hg : M.mem g X)
    (fi : Sc_index_d κ A f) (gi : Sc_index_d κ B g) :
    ∃ e, M.mem e X ∧ M.IsSetInjectionFromTo I e D κ := by
  obtain ⟨q, hq, qi⟩ := source.finite_index_l hZF fi.ordinal
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨o, ho, hoω⟩ := source.omega.1.2 z hzω
  obtain ⟨n, hn, hnω⟩ := source.omega.1.2 o hoω
  have hzo : z ≠ o := by intro eq; subst o; exact hz z ho.predecessor_mem
  obtain ⟨c, code⟩ := source.code
  let ρ : Env M 9 := ⟨Fin.cases A (Fin.cases B (Fin.cases f (Fin.cases g
    (Fin.cases κ (Fin.cases z (Fin.cases o (Fin.cases K (fun _ => q)))))))), fun _ => ω⟩
  let φ : BinarySchema 9 := { body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
    (Formula.existsMem (.bound 8) (Formula.existsMem (.bound 9) (Formula.existsMem (.bound 13)
      (.conj (kpair0_m (.bound 6) (.bound 4) (.bound 3))
        (.conj (rd_entry0_m (.bound 4) (.bound 2) (.bound 9))
          (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 10))
            (.conj (rd_entry0_m (.bound 12) (.bound 2) .newest)
              (.conj (rd_entry0_m (.bound 13) (.bound 1) .newest)
                (rd_entry0_m .newest (.bound 5) (.bound 15))))))))))) }
  have read u i : φ.denote ρ u i ↔ ∃ a, M.mem a A ∧ ∃ b, M.mem b B ∧
      ∃ x, M.mem x κ ∧ ∃ y, M.mem y κ ∧ ∃ s, M.mem s K ∧ KPair_d M u a b ∧
        Rd_entry_d a x f ∧ Rd_entry_d b y g ∧ Rd_entry_d z x s ∧ Rd_entry_d o y s ∧ Rd_entry_d s i q := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨e, he, fn, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory φ
    (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
      (.conj (kpair0_delta_l ..) (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..)
        (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))))) ρ
    (Fin.cases hA (Fin.cases hB (Fin.cases hf (Fin.cases hg (Fin.cases source.cardinal_mem
      (Fin.cases (source.transitive ω source.omega_mem z hzω) (Fin.cases (source.transitive ω source.omega_mem o hoω)
        (Fin.cases source.finite.mem_l (fun _ => hq))))))))) hD source.cardinal_mem (fun u hu => by
      obtain ⟨a, ha, b, hb, pair⟩ := (product u).mp hu
      obtain ⟨x, hx, hax⟩ := fi.total a ha
      obtain ⟨y, hy, hby⟩ := gi.total b hb
      obtain ⟨s, sf, sz, so⟩ := ep_two_values_l hZF hzo ((hn z).mpr (Or.inl ho.predecessor_mem)) hn.predecessor_mem hx hy
      have hs := ((source.finite_l (ZF.modelsKP hZF)) s).mpr ⟨n, hnω, fn0_function_l (ZF.modelsKP hZF) sf⟩
      obtain ⟨i, hi, hsi⟩ := qi.1.2.2 s hs
      exact ⟨i, hi, (read u i).mpr ⟨a, ha, b, hb, x, hx, y, hy, s, hs, pair, hax, hby, sz, so, hsi⟩⟩)
  refine ⟨e, he, fn0_function_l (ZF.modelsKP hZF) fn, fun u v i hu hv => ?_⟩
  obtain ⟨a, ha, b, hb, x, hx, y, hy, s, hs, up, hax, hby, sz, so, hsi⟩ := (read u i).mp (select u i hu)
  obtain ⟨a', ha', b', hb', x', hx', y', hy', s', hs', vp, hax', hby', sz', so', hsi'⟩ := (read v i).mp (select v i hv)
  have eq := qi.2 s s' i hsi hsi'
  subst s'
  obtain ⟨_, _, sf⟩ := ((source.finite_l (ZF.modelsKP hZF)) s).mp hs
  have ex := sf.1.2 z x x' sz sz'
  have ey := sf.1.2 o y y' so so'
  have ea := fi.injective a ha a' ha' x hx hax (ex.symm ▸ hax')
  have eb := gi.injective b hb b' hb' y hy hby (ey.symm ▸ hby')
  exact kpair_unique_l M hZF.1 up (ea.symm ▸ eb.symm ▸ vp)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 源内可数支撑族的源内单射覆盖列

用一项自然数列编码 ω 本身，两项自然数列编码支撑族的逐坐标求值。
已有有限列编号给出像集的源内 ω 编号，再在源内施行 Cantor–Bernstein。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ec_source_cover_l {ω κ K X R L S A : M.Domain} (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (hL : M.mem L X) (hωL : M.MemberSubset ω L) (hA : M.mem A X)
    (seq : Fseq_space_d I ω L S) (fn : Fn0_d ω S A) : ∃ f, M.mem f X ∧ M.IsSetInjectionFromTo I f ω L ∧
      ∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f := by
  obtain ⟨c, code⟩ := source.code
  obtain ⟨S', hS', seq'⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 L hL
  have hS : M.mem S X := hZF.1.eq_of_same_members S' S (fun f => (seq' f).trans (seq f).symm) ▸ hS'
  obtain ⟨K₀, small⟩ := source.rebase_l source.omega_mem (fun _ h => h) (source.cardinal_small.mono_mem_l I code source.omega_mem source.below)
  obtain ⟨ι, hι, index⟩ := small.finite_index_l hZF (source.omega.isOrdinal (ZF.modelsKP hZF))
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨o, ho, hoω⟩ := source.omega.1.2 z hzω
  obtain ⟨t, ht, htω⟩ := source.omega.1.2 o hoω
  have hzo : z ≠ o := fun eq => hz z (eq ▸ ho.predecessor_mem)
  have hot : o ≠ t := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) o (eq.symm ▸ ht.predecessor_mem)
  let value k x := (Fn0_d o ω k ∧ Rd_entry_d z x k) ∨ (Fn0_d t ω k ∧
    ∃ i, M.mem i ω ∧ ∃ j, M.mem j ω ∧ ∃ a, M.mem a S ∧
      Rd_entry_d z i k ∧ Rd_entry_d o j k ∧ Rd_entry_d i a A ∧ Rd_entry_d j x a)
  have bounded k x (hv : value k x) : M.mem x L := by
    rcases hv with ⟨hk, hx⟩ | ⟨_, _, _, j, _, a, ha, _, _, _, hx⟩
    · exact hωL x (hk.bound_l hx).2
    · obtain ⟨_, _, hf⟩ := (seq a).mp ha
      exact hf.output_mem_of_pairMember hx
  have unique k x y (hx : value k x) (hy : value k y) : x = y := by
    rcases hx with ⟨hk, hzx⟩ | ⟨hk, i, _, j, _, a, ha, hzi, hoj, hia, hjx⟩ <;>
      rcases hy with ⟨hk', hzy⟩ | ⟨hk', i', _, j', _, a', _, hzi', hoj', hia', hjy⟩
    · exact (fn0_function_l (ZF.modelsKP hZF) hk).1.2 z x y hzx hzy
    · exact (hot (hk.domain_eq_l hZF.1 hk')).elim
    · exact (hot (hk'.domain_eq_l hZF.1 hk)).elim
    · have ei := (fn0_function_l (ZF.modelsKP hZF) hk).1.2 z i' i hzi' hzi
      have ej := (fn0_function_l (ZF.modelsKP hZF) hk).1.2 o j' j hoj' hoj
      subst i' j'
      have ea := (fn0_function_l (ZF.modelsKP hZF) fn).1.2 i a' a hia' hia
      subst a'
      obtain ⟨_, _, hf⟩ := (seq a).mp ha
      exact hf.1.2 j x y hjx hjy
  let ρ : Env M 6 := ⟨Fin.cases A (Fin.cases S (Fin.cases t (Fin.cases o (Fin.cases z (fun _ => ω))))), fun _ => ω⟩
  let φ : BinarySchema 6 := {
    body := .disj (.conj (fn0_m (.bound 5) (.bound 7) (.bound 1)) (rd_entry0_m (.bound 6) .newest (.bound 1)))
      (.conj (fn0_m (.bound 4) (.bound 7) (.bound 1)) (Formula.existsMem (.bound 7) (Formula.existsMem (.bound 8)
        (Formula.existsMem (.bound 5) (.conj (rd_entry0_m (.bound 9) (.bound 2) (.bound 4))
          (.conj (rd_entry0_m (.bound 8) (.bound 1) (.bound 4))
            (.conj (rd_entry0_m (.bound 2) .newest (.bound 5)) (rd_entry0_m (.bound 1) (.bound 3) .newest)))))))) }
  have delta : φ.body.IsDelta0 := .disj (.conj (fn0_delta_l ..) (rd_entry0_delta_l ..))
    (.conj (fn0_delta_l ..) (.existsMem _ (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))))
  have sat k x : φ.denote ρ k x ↔ value k x := by
    simp only [φ, BinarySchema.denote, value, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_existsMem_iff, fn0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  let e : Fin 8 → Fin 9 := Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))
  let e' : Fin 8 → Fin 10 := Fin.cases 0 (Fin.cases 2 (fun i => i.succ.succ.succ.succ))
  let η := ρ.push L
  let ψ : BinarySchema 7 := {
    body := .disj (φ.body.rename e) (.conj (.neg (Formula.existsMem (.bound 2) (φ.body.rename e')))
      (Formula.extensionalEq .newest (.bound 7)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have read k x : ψ.denote η k x ↔ value k x ∨ ((¬ ∃ y, M.mem y L ∧ value k y) ∧ x = z) := by
    have point : Formula.satisfies ((η.push k).push x) (φ.body.rename e) ↔ value k x :=
      (Formula.satisfies_rename ..).trans ((Formula.closed_env_l φ.body φ.freeClosed
        (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))).trans (sat k x))
    have point' y : Formula.satisfies (((η.push k).push x).push y) (φ.body.rename e') ↔ value k y :=
      (Formula.satisfies_rename ..).trans ((Formula.closed_env_l φ.body φ.freeClosed
        (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))).trans (sat k y))
    simp only [ψ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_existsMem_iff, point, point', Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨F, hFX, ff, select⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory ψ
    (.disj (delta.rename_l e) (.conj (.neg (.existsMem _ (delta.rename_l e'))) (.atom ..))) η
    (Fin.cases hL (Fin.cases hA (Fin.cases hS (Fin.cases (source.transitive ω source.omega_mem t htω)
      (Fin.cases (source.transitive ω source.omega_mem o hoω) (Fin.cases (source.transitive ω source.omega_mem z hzω)
        (fun _ => source.omega_mem))))))) small.finite.mem_l hL (fun k _ => by
      classical
      by_cases h : ∃ x, M.mem x L ∧ value k x
      · obtain ⟨x, hx, hv⟩ := h
        exact ⟨x, hx, (read k x).mpr (Or.inl hv)⟩
      · exact ⟨z, hωL z hzω, (read k z).mpr (Or.inr ⟨h, rfl⟩)⟩)
  have realize k x (hk : M.mem k K₀) (hv : value k x) : Rd_entry_d k x F := by
    obtain ⟨y, _, hky⟩ := ff.2.1 k hk
    rcases (read k y).mp (select k y hky) with hy | ⟨no, _⟩
    · exact unique k y x hy hv ▸ hky
    · exact (no ⟨x, bounded k x hv, hv⟩).elim
  obtain ⟨C, hC, range⟩ := sc_range_source_l hZF source.omega source.transitive code source.theory hFX
  have cl x (hx : M.mem x C) : M.mem x L := ((range x).mp hx).elim fun _ h => (ff.bound_l h).2
  have omega x (hx : M.mem x ω) : M.mem x C := by
    obtain ⟨k, _, _, _, kf, kv⟩ := sc_constant_l hZF source.omega source.transitive code source.theory
      (source.transitive ω source.omega_mem o hoω) (source.transitive ω source.omega_mem x hx)
    have kω := kf.retarget_l (fun i y hiy => ((kv i y).mp hiy).2 ▸ hx)
    exact (range x).mpr ⟨k, realize k x (((small.finite_l (ZF.modelsKP hZF)) k).mpr ⟨o, hoω, fn0_function_l (ZF.modelsKP hZF) kω⟩)
      (Or.inl ⟨kω, (kv z x).mpr ⟨ho.predecessor_mem, rfl⟩⟩)⟩
  have covered i a j x (hia : Rd_entry_d i a A) (hjx : Rd_entry_d j x a) : M.mem x C := by
    obtain ⟨n, hn, ha⟩ := (seq a).mp (fn.bound_l hia).2
    have hi := (fn.bound_l hia).1
    have hj := source.omega.transitive (ZF.modelsKP hZF) n hn j (ha.input_mem_of_pairMember hjx)
    obtain ⟨k, kf, k0, k1⟩ := ep_two_values_l hZF hzo ((ht z).mpr (Or.inl ho.predecessor_mem)) ht.predecessor_mem hi hj
    exact (range x).mpr ⟨k, realize k x (((small.finite_l (ZF.modelsKP hZF)) k).mpr ⟨t, htω, fn0_function_l (ZF.modelsKP hZF) kf⟩)
      (Or.inr ⟨kf, i, hi, j, hj, a, (fn.bound_l hia).2, k0, k1, hia, hjx⟩)⟩
  obtain ⟨j, hj, cj⟩ := sc_index_image_l hZF source.omega source.transitive code source.theory small.finite.mem_l hC hFX
    source.omega_mem hι (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (source.omega.isOrdinal (ZF.modelsKP hZF)) index)
    (ff.retarget_l (fun k x hkx => (range x).mpr ⟨k, hkx⟩)) (fun x hx => ((range x).mp hx).imp fun k hk => ⟨(ff.bound_l hk).1, hk⟩)
  obtain ⟨j', hj', inj⟩ := cj.restrict_l hZF source.omega source.transitive code source.theory hC source.omega_mem hj
  let equal : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ε : Env M 0 := ⟨Fin.elim0, fun _ => ω⟩
  have eqs a b : equal.denote ε a b ↔ a = b := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨i, hi, fi, is⟩ := sc_uniform_source_l hZF source.omega source.transitive code source.theory equal (.atom ..)
    ε (fun k => Fin.elim0 k) source.omega_mem hC (fun x hx => ⟨x, omega x hx, (eqs x x).mpr rfl⟩)
  have ii : M.IsSetInjectionFromTo I i ω C := ⟨fn0_function_l (ZF.modelsKP hZF) fi,
    fun a b x ha hb => ((eqs a x).mp (is a x ha)).trans ((eqs b x).mp (is b x hb)).symm⟩
  obtain ⟨f, hf, bij⟩ := sc_cantor_bernstein_l hZF source.omega source.transitive code source.theory source.omega_mem hC hi hj' ii inj
  exact ⟨f, hf, ⟨bij.1.1.mono_target_l I cl, bij.1.2⟩,
    fun i a j x hia hjx => (bij.2 x (covered i a j x hia hjx)).imp fun _ h => h.2⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 复制时的有限幂、坐标与测度成员对应 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Ea_maps_d (ω κ X π σ : M.Domain) : Prop := ∀ n D A A', M.mem n ω → Ep_space_d κ n D →
  M.mem A X → M.MemberSubset A D → Rd_entry_d A A' π → Rd_entry_d A A' σ

/-- 全部有限单射支撑的集合沿初等嵌入传输，包含目标中的新支撑。 -/
theorem ep_indices_map_l {ω X R Y S c d σ L L' J J' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hσ : Smap_d I ω c d X Y σ)
    (theory : Sc_theory_d I ω Y S) (hωX : M.mem ω X)
    (hL : Rd_entry_d L L' σ) (hJ : Rd_entry_d J J' σ) (indices : ∀ a, M.mem a J ↔ Ei_d ω L a) :
    ∀ a, M.mem a J' ↔ Ei_d ω L' a := by
  have ωσ := hσ.omega_l I hZF hω hX hY hm hn hωX
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (ei_m (.bound 3) (.bound 2) .newest)
  have tr := hσ.forall_delta_l hZF hω hX hY hm hn φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) (.iff (.mem ..) (ei_delta_l ..))
    ⟨Fin.cases J (Fin.cases L (fun _ => ω)), fun _ => ω⟩
    ⟨Fin.cases J' (Fin.cases L' (fun _ => ω)), fun _ => ω⟩ (Fin.cases hJ (Fin.cases hL (fun _ => ωσ)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, ei_sat_l hZF.1] at tr
  have read := tr.mp (fun a _ => indices a)
  exact fun a => ⟨fun ha => (read a (hY J' (hσ.1.1.output_mem_of_pairMember hJ) a ha)).mp ha, fun ha => by
    obtain ⟨n, hnω, fn, inj⟩ := ha
    have owned := sc_finite_function_l (ZF.modelsKP hZF) hω hY (theory.algebra_l I (ZF.modelsKP hZF) hY hn).pair (theory.algebra_l I (ZF.modelsKP hZF) hY hn).union (hσ.1.1.output_mem_of_pairMember ωσ)
      (hY L' (hσ.1.1.output_mem_of_pairMember hL)) hnω fn
    exact (read a owned).mpr ⟨n, hnω, fn, inj⟩⟩

theorem ep_space_map_l {ω μ μ' κ κ' K K' X R Y S c d π n D D' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hκ : M.PairMember I κ κ' π) (hnω : M.mem n ω) (space : Ep_space_d κ n D)
    (hD : M.PairMember I D D' π) : Ep_space_d κ' n D' := by
  have fixed := hπ.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem n hnω
  let φ : Formula 1 4 := .iff (.mem .newest (.bound 1)) (fn0_m (.bound 3) (.bound 2) .newest)
  have tr := hπ.forall_delta_l hZF source.omega source.transitive target.transitive hm hn φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) (.iff (.mem _ _) (fn0_delta_l ..))
    ⟨Fin.cases D (Fin.cases κ (fun _ => n)), fun _ => n⟩
    ⟨Fin.cases D' (Fin.cases κ' (fun _ => n)), fun _ => n⟩ (Fin.cases hD (Fin.cases hκ (fun _ => fixed)))
  simp only [φ, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, fn0_sat_l hZF.1] at tr
  have read := tr.mp (fun f _ => space f)
  intro f
  exact ⟨fun hf => (read f (target.transitive D' (hπ.1.1.output_mem_of_pairMember hD) f hf)).mp hf,
    fun hf => (read f (sc_finite_function_l (ZF.modelsKP hZF) target.omega target.transitive (target.algebra_l (ZF.modelsKP hZF)).pair (target.algebra_l (ZF.modelsKP hZF)).union target.omega_mem
      (target.transitive κ' (hπ.1.1.output_mem_of_pairMember hκ)) hnω hf)).mpr hf⟩

theorem ec_measure_image_l {ω c d N R N' S σ F F' a a' U V A A' : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c N R) (hn : Smdl_d I d N' S) (hσ : Smap_d I ω c d N N' σ)
    (hF : M.PairMember I F F' σ) (ha : M.PairMember I a a' σ) (hA : M.PairMember I A A' σ)
    (hU : Rf_val_d I N R a U F) (hV : Rf_val_d I N' S a' V F')
    (unique : ∀ x y z, Rf_val_d I N' S x y F' → Rf_val_d I N' S x z F' → y = z) :
    Rd_entry_d A U R ↔ Rd_entry_d A' V S := by
  obtain ⟨U', _, hUU⟩ := hσ.1.1.2.2 U (hU.bounds_l I).2.1
  have entry := hU.map_l I hZF hω hm hn hσ ha hUU hF
  have eq := unique a' U' V entry hV
  exact eq ▸ hσ.relation_l I hZF hω hm hn hA hUU

theorem ec_support_image_l {ω c d N R N' S σ L L' a a' : M.Domain}
    (hω : M.IsOmega ω) (hN : M.TransitiveSet N) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c N R) (hn : Smem_d I d N' S) (hσ : Smap_d I ω c d N N' σ)
    (hωN : M.mem ω N) (hL : M.PairMember I L L' σ) (haa : M.PairMember I a a' σ)
    (ha : Ei_d ω L a) : Ei_d ω L' a' := by
  obtain ⟨n, hnω, ha, inj⟩ := ha
  have image := hσ.finite_injection_l hZF hω hN hN' hm hn hωN hnω hL haa
    ⟨fn0_function_l (ZF.modelsKP hZF) ha, inj⟩
  exact ⟨n, hnω, fn0_of_function_l (ZF.modelsKP hZF) image.1, image.2⟩

theorem ec_index_image_l {ω c d N R N' S σ L L' a a' b b' q m n : M.Domain}
    (hω : M.IsOmega ω) (hN : M.TransitiveSet N) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c N R) (hn : Smem_d I d N' S) (hσ : Smap_d I ω c d N N' σ)
    (theory : Sc_theory_d I ω N R) (hωN : M.mem ω N) (hL : Rd_entry_d L L' σ)
    (haa : Rd_entry_d a a' σ) (hbb : Rd_entry_d b b' σ)
    (hmω : M.mem m ω) (hnω : M.mem n ω) (hq : Fn0_d m n q) (hb : Fn0_d n L b) (ha : Cp0_d m n L q b a) :
    Fn0_d n L' b' ∧ Cp0_d m n L' q b' a' := by
  have qω := hq.mono_target_l (hω.transitive (ZF.modelsKP hZF) n hnω)
  have hqN := sc_finite_function_l (ZF.modelsKP hZF) hω hN (theory.algebra_l I (ZF.modelsKP hZF) hN hm).pair (theory.algebra_l I (ZF.modelsKP hZF) hN hm).union hωN (hN ω hωN) hmω qω
  have hqq := hσ.finite_fixed_l hZF hω hN hN' hm hn hωN hmω hqN qω
  have nat := hσ.natural_l hZF hω hN hN' hm hn hωN
  exact ⟨(hσ.function_l hZF hω hN hN' hm hn (nat n hnω) hL hbb).mp hb,
    (hσ.composition_l hZF hω hN hN' hm hn (nat m hmω) (nat n hnω) hL hqq hbb haa).mp ha⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双映射复制的实际分量

支撑由所属模型的 σ 搬运，代表由施加源的 π 搬运。两图在有限 κ 幂的
源子集上相同，配合 σ(F)=F′，实际推出测度成员对应，再构造完整初等复制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

def Ec_class_d (π B C : M.Domain) : Prop := ∃ f g, M.mem f B ∧ M.mem g C ∧ Rd_entry_d f g π

def ec_class_m {d} (π B C : Term d) : Formula 1 d := Formula.existsMem B (Formula.existsMem C.weaken
  (rd_entry_m (.bound 1) .newest π.weaken.weaken))
derive_free_closed ec_class_m

theorem ec_class_sat_l (hE : Extensional M) {d} (ρ : Env M d) (π B C : Term d) :
    Formula.satisfies ρ (ec_class_m π B C) ↔ Ec_class_d (π.eval ρ) (B.eval ρ) (C.eval ρ) := by
  simp only [ec_class_m, Ec_class_d, Formula.satisfies_existsMem_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨f, hf, g, hg, h⟩ => ⟨f, g, hf, hg, h⟩, fun ⟨f, g, hf, hg, h⟩ => ⟨f, hf, g, hg, h⟩⟩

theorem ec_component_l (hZF : M.Models ZF)
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F' a a' o o' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d Y S)
    (hπ : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X Y π)
    (hκ : Rd_entry_d κ κ' π) (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N')
    (h₀ : Smem_d (kp_pair_l (ZF.modelsKP hZF)) b N R₀)
    (h₁ : Smem_d (kp_pair_l (ZF.modelsKP hZF)) b' N' R₁)
    (hσ : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω b b' N N' σ)
    (hωN : M.mem ω N) (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' Y F') (agree : Ea_maps_d ω κ X π σ)
    (haa : Rd_entry_d a a' σ)
    (hM : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F a o)
    (hM' : Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' L' Y S F' a' o') :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ C T C' T' e, Smdl_d I o C T ∧ Smdl_d I o' C' T' ∧ Smap_d I ω o o' C C' e ∧
      (∀ B D, Rd_entry_d B D e ↔ M.mem B C ∧ M.mem D C' ∧ Ec_class_d π B D) ∧
      ∀ B D f g, M.mem B C → M.mem D C' → Ec_class_d π B D → M.mem f B → Rd_entry_d f g π → M.mem g D := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨n, D, U, G, p, C, T, hnω, ha, space, haU, hG, model⟩ := hM
  obtain ⟨n', E, V, H, p', C', T', _, ha', space', haV, hH, model'⟩ := hM'
  have hna := (hσ.function_l hZF source.omega owner owner' h₀ h₁
    (hσ.natural_l hZF source.omega owner owner' h₀ h₁ hωN n hnω) hL haa).mp ha
  have en := ha'.domain_eq_l hZF.1 hna
  subst n'
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D (source.space_mem_l hZF hnω space)
  have image := ep_space_map_l hZF source target hm hn hπ hκ hnω space hDD
  have eD := hZF.1.eq_of_same_members D' E (fun s => (image s).trans (space' s).symm)
  subst D'
  have hu := family.at_l hZF.1 haU ha space
  have hv := family'.at_l hZF.1 haV ha' space'
  obtain ⟨P, U', hp, hu', us, model₀⟩ := rs_restrict_model_l hZF source.omega source.transitive hm source.theory
    (source.space_mem_l hZF hnω space) hu hG model
  obtain ⟨Q, V', hq, hv', vs, model₁⟩ := rs_restrict_model_l hZF target.omega target.transitive hn target.theory
    (target.space_mem_l hZF hnω space') hv hH model'
  have measures A A' (hA : M.mem A P) (hAA : Rd_entry_d A A' π) : M.mem A U' ↔ M.mem A' V' := by
    have hAQ := (hq A').mpr ⟨hπ.1.1.output_mem_of_pairMember hAA,
      (hπ.subset_l hZF source.omega source.transitive target.transitive hm hn hAA hDD).mp ((hp A).mp hA).2⟩
    have copied := agree n D A A' hnω space ((hp A).mp hA).1 ((hp A).mp hA).2 hAA
    have hFN := hσ.1.1.input_mem_of_pairMember hF
    have hFN' := hσ.1.1.output_mem_of_pairMember hF
    have old := (rf_val_mem_l I hZF.1 owner h₀ hFN).mpr haU
    have next := (rf_val_mem_l I hZF.1 owner' h₁ hFN').mpr haV
    have raw := ec_measure_image_l hZF source.omega h₀.1 h₁.1 hσ hF haa copied old next
      (fun x y z h g => family'.function x y z
        ((rf_val_mem_l I hZF.1 owner' h₁ hFN').mp h) ((rf_val_mem_l I hZF.1 owner' h₁ hFN').mp g))
    have eq : M.mem A U ↔ M.mem A' V :=
      ⟨fun h => ((h₁.2 A' V).mp (raw.mp ((h₀.2 A U).mpr
        ⟨hσ.1.1.input_mem_of_pairMember copied, (old.bounds_l I).2.1, h⟩))).2.2,
       fun h => ((h₀.2 A U).mp (raw.mpr ((h₁.2 A' V).mpr
        ⟨hσ.1.1.output_mem_of_pairMember copied, (next.bounds_l I).2.1, h⟩))).2.2⟩
    exact ((us A).trans ⟨And.right, fun h => ⟨hA, h⟩⟩).trans
      (eq.trans ((vs A').trans ⟨And.right, fun h => ⟨hAQ, h⟩⟩).symm)
  obtain ⟨Qf, e, hf, fs, he, lift⟩ := rs_copy_embedding_l hZF source.omega source.transitive target.transitive hm hn hπ
    source.theory (source.uniform_l hZF hnω space) (target.uniform_l hZF hnω space') hDD hp hq hu' hv' measures hG hH model₀ model₁
  have spec : ∀ B D, Rd_entry_d B D e ↔ M.mem B C ∧ M.mem D C' ∧ Ec_class_d π B D := by
    intro B D
    constructor
    · intro hBD
      have hBC := he.1.1.input_mem_of_pairMember hBD
      obtain ⟨f, hfp⟩ := (model.map.range B).mp hBC
      obtain ⟨g, hg, hfg⟩ := hf.2.2 f (model.map.projection.input_mem_of_pairMember hfp)
      obtain ⟨D', _, hgp⟩ := model'.map.projection.2.2 g hg
      have eq := he.1.1.1.2 B D' D (lift f g B D' hfg hfp hgp) hBD
      exact ⟨hBC, he.1.1.output_mem_of_pairMember hBD, f, g, model.map.representative_l I hu.base hfp,
        eq ▸ model'.map.representative_l I hv.base hgp, ((fs f g).mp hfg).2⟩
    · rintro ⟨hB, hD, f, g, hfB, hgD, hfg⟩
      have hfp := model.map.member_l I hZF.1 hu.base hB hfB
      have hgp := model'.map.member_l I hZF.1 hv.base hD hgD
      exact lift f g B D ((fs f g).mpr ⟨model.map.projection.input_mem_of_pairMember hfp, hfg⟩) hfp hgp
  refine ⟨C, T, C', T', e, model.code, model'.code, he, spec, fun B D f g hB hD hc hfB hfg => ?_⟩
  have hfp := model.map.member_l I hZF.1 hu.base hB hfB
  have hfg' := (fs f g).mpr ⟨model.map.projection.input_mem_of_pairMember hfp, hfg⟩
  obtain ⟨D', _, hgp⟩ := model'.map.projection.2.2 g (hf.output_mem_of_pairMember hfg')
  have eq := he.1.1.1.2 B D' D (lift f g B D' hfg' hfp hgp) ((spec B D).mpr ⟨hB, hD, hc⟩)
  exact eq ▸ model'.map.representative_l I hv.base hgp

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际源中任意字母表的树枝绝对性

先在源内分离真实子边，再用独立的枝反射取得源内下降节点列。
其全部前缀构成无死节点树；最后逐坐标读取节点列，得到源内的总分支图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.tree_edges_l {ω κ K X R A J T : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (hA : M.mem A X) (hT : M.mem T X)
    (hJ : Fseq_space_d I ω A J) (tree : Tree_d J T) : ∃ E, M.mem E X ∧ Edge_d I ω T E := by
  obtain ⟨P, hPX, hp⟩ := source.square_l hZF hT
  obtain ⟨c, hc⟩ := source.code
  let ρ : Env M 3 := ⟨Fin.cases T (Fin.cases ω (fun _ => A)), fun _ => T⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
    (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (tb_step_m (.bound 4) (.bound 5) .newest (.bound 1)))) }
  have sat p : φ.denote ρ p ↔ ∃ t, M.mem t T ∧ ∃ s, M.mem s T ∧ KPair_d M p t s ∧ Tb_step_d ω A s t := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, tb_step_sat_l hZF.1]; rfl
  obtain ⟨E, hEX, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (tb_step_delta_l ..))))
    ρ (Fin.cases hT (Fin.cases source.omega_mem (fun _ => hA))) hPX
  refine ⟨E, hEX, fun p he => (hp p).mp ((spec p).mp he).1 |>.elim fun t ht => ht.2.elim fun s hs => ⟨t, s, hs.2⟩, ?_⟩
  intro s t
  constructor
  · rintro ⟨p, hpair, he⟩
    obtain ⟨u, hu, v, hv, hp', hs⟩ := (sat p).mp ((spec p).mp he).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hpair hp'
    exact ⟨hv, hu, (tb_step_l hZF source.omega hJ (tree.1 s hv) (tree.1 t hu)).mp hs⟩
  · rintro ⟨hs, ht, hst⟩
    obtain ⟨p, hpair⟩ := (I).total t s
    exact ⟨p, hpair, (spec p).mpr ⟨(hp p).mpr ⟨t, ht, s, hs, hpair⟩,
      (sat p).mpr ⟨t, ht, s, hs, hpair, (tb_step_l hZF source.omega hJ (tree.1 s hs) (tree.1 t ht)).mpr hst⟩⟩⟩

theorem Ep_source_d.tree_branch_l {ω κ K X R A J T f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (branches : Sc_branch_d ω X) (hA : M.mem A X) (hT : M.mem T X)
    (hJ : Fseq_space_d I ω A J) (tree : Tree_d J T) (hf : M.IsSetFunctionFromTo I f ω A)
    (branch : Branch_d J T f) : ∃ g, M.mem g X ∧ M.IsSetFunctionFromTo I g ω A ∧ Branch_d J T g := by
  have hω := source.omega
  -- 子边及背景前缀列实际存在，再由独立的枝反射取得源内节点列。
  obtain ⟨E, hEX, edges⟩ := source.tree_edges_l hZF hA hT hJ tree
  obtain ⟨G, hGX, hG, desc⟩ := branches T E hT hEX (tree_branch_desc_l I hZF hω hJ hf branch edges)
  have fn := fn0_function_l (ZF.modelsKP hZF) hG
  have next i j s t (hs : M.SuccessorOf j i) (hi : Rd_entry_d i s G) (hj : Rd_entry_d j t G) : Step_d I ω s t :=
    ((edges.2 s t).mp (desc i j s t hs hi hj)).2.2
  have inc := ZF.cc_increasing_of_successor_l I hZF hω fn (fun i j s t hs hi hj => by
    obtain ⟨n, hn, hsn⟩ := (hJ s).mp (tree.1 s (hG.bound_l hi).2)
    obtain ⟨m, hm, htm⟩ := (hJ t).mp (tree.1 t (hG.bound_l hj).2)
    exact ((tree_step_iff_l I hZF hω hn hm hsn htm).mp (next i j s t hs hi hj)).2)
  obtain ⟨J', hJX, specJ⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 A hA
  have eqJ := hZF.1.eq_of_same_members J' J (fun s => (specJ s).trans (hJ s).symm)
  have hJX : M.mem J X := eqJ ▸ hJX
  obtain ⟨c, hc⟩ := source.code
  -- 收集节点列的全部前缀，允许下降链从非空节点开始。
  let ρ : Env M 3 := ⟨Fin.cases ω (Fin.cases T (fun _ => G)), fun _ => ω⟩
  let φ : UnarySchema 3 := { body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3)
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 5)) (Formula.subset (.bound 2) .newest))) }
  have sat s : φ.denote ρ s ↔ ∃ i, M.mem i ω ∧ ∃ q, M.mem q T ∧ Rd_entry_d i q G ∧ M.MemberSubset s q := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      rd_entry0_sat_l hZF.1, Formula.satisfies_subset_iff]; rfl
  obtain ⟨P, hPX, spec⟩ := sc_separate_source_l I hZF hω source.transitive hc source.theory φ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (.atom _ _ _))))
    ρ (Fin.cases source.omega_mem (Fin.cases hT (fun _ => hGX))) hJX
  have read s : M.mem s P ↔ M.mem s J ∧ ∃ i, M.mem i ω ∧ ∃ q, M.mem q T ∧ Rd_entry_d i q G ∧ M.MemberSubset s q :=
    (spec s).trans (and_congr_right fun _ => sat s)
  have sub s (hs : M.mem s P) : M.mem s T := by
    obtain ⟨hsJ, _, _, q, hq, _, hsq⟩ := (read s).mp hs
    exact tree.2 q hq s hsJ hsq
  have pruned s (hs : M.mem s P) : ∃ t, M.mem t P ∧ Tb_step_d ω A s t := by
    obtain ⟨hsJ, i, hi, q, hq, hiq, hsq⟩ := (read s).mp hs
    obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
    obtain ⟨v, hv, hjv⟩ := hG.2.1 j hjω
    obtain ⟨n, hn, hsn⟩ := (hJ s).mp hsJ
    obtain ⟨l, hl, hql⟩ := (hJ q).mp (tree.1 q hq)
    obtain ⟨m, hm, hvm⟩ := (hJ v).mp (tree.1 v hv)
    obtain ⟨hml, hqv⟩ := (tree_step_iff_l I hZF hω hl hm hql hvm).mp (next i j q v hj hiq hjv)
    have hnl : M.MemberSubset n l := fun a ha => by
      obtain ⟨b, _, hab⟩ := hsn.2.2 a ha
      exact hql.input_mem_of_pairMember (hab.elim fun p hp => ⟨p, hp.1, hsq p hp.2⟩)
    have hnm : M.mem n m := by
      rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn l hl with e | e | e
      · exact (hZF.1.eq_of_same_members n l e).symm ▸ hml.predecessor_mem
      · exact (hml n).mpr (Or.inl e)
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) l (hnl l e)).elim
    obtain ⟨u, hu, huω⟩ := hω.1.2 n hn
    have hum : M.MemberSubset u m := fun a ha => ((hu a).mp ha).elim
      (fun ha => (hml a).mpr (Or.inl (hnl a ha))) (fun e => (hZF.1.eq_of_same_members a n e).symm ▸ hnm)
    obtain ⟨t, htv⟩ := ZF.exists_restriction hZF I v u
    have htu := htv.isSetFunctionFromTo hvm hum
    have hst := ds_prefix_mono_l I hsn htu.1 ((ds_restrict_iff_l I hsn hvm.1).mpr
      (fun p hp => hqv p (hsq p hp))) htv (fun a ha => (hu a).mpr (Or.inl ha))
    exact ⟨t, (read t).mpr ⟨(hJ t).mpr ⟨u, huω, htu⟩, j, hjω, v, hv, hjv,
      (ds_restrict_iff_l I htu hvm.1).mp htv⟩,
      n, hn, u, huω, fn0_of_function_l (ZF.modelsKP hZF) hsn, fn0_of_function_l (ZF.modelsKP hZF) htu, hu, hst⟩
  let η : Env M 3 := ⟨Fin.cases P (Fin.cases ω (fun _ => A)), fun _ => P⟩
  -- 先用无死节点性得到每个长度的前缀，再在源内逐坐标收集同一条枝。
  let ψ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 2)) (tb_step_m (.bound 3) (.bound 4) (.bound 1) .newest) }
  have choose s t : ψ.denote η s t ↔ M.mem t P ∧ Tb_step_d ω A s t := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, tb_step_sat_l hZF.1]; rfl
  obtain ⟨F, _, hF, select⟩ := sc_uniform_source_l hZF hω source.transitive hc source.theory ψ
    (.conj (.mem _ _) (tb_step_delta_l ..)) η (Fin.cases hPX (Fin.cases source.omega_mem (fun _ => hA))) hPX
    hPX (fun s hs => (pruned s hs).imp fun t ht => ⟨ht.1, (choose s t).mpr ht⟩)
  have fnF := fn0_function_l (ZF.modelsKP hZF) hF
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨q, hq, hzq⟩ := hG.2.1 z hzω
  have hzP := (read z).mpr ⟨(hJ z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩, z, hzω, q, hq, hzq, fun p hp => (hz p hp).elim⟩
  obtain ⟨f₀, _, path⟩ := ds_path_l I hZF hω (fun s hs => (hJ s).mp ((read s).mp hs).1) fnF hz hzP
    (fun s t h => (tb_step_l hZF hω hJ ((read s).mp (hF.bound_l h).1).1
      ((read t).mp ((choose s t).mp (select s t h)).1).1).mp ((choose s t).mp (select s t h)).2)
  -- 原图列中的节点两两相容；逐坐标统一化不会改变任何已出现的值。
  have unique i n m s t x y (hs : Rd_entry_d n s G) (ht : Rd_entry_d m t G)
      (hx : Rd_entry_d i x s) (hy : Rd_entry_d i y t) : x = y := by
    obtain ⟨_, _, hsn⟩ := (hJ s).mp (tree.1 s (hG.bound_l hs).2)
    obtain ⟨_, _, htm⟩ := (hJ t).mp (tree.1 t (hG.bound_l ht).2)
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n (hG.bound_l hs).1 m (hG.bound_l ht).1 with e | e | e
    · have en := hZF.1.eq_of_same_members n m e
      subst m
      exact htm.1.2 i x y (fn.1.2 n s t hs ht ▸ hx) hy
    · exact htm.1.2 i x y (hx.elim fun p hp => ⟨p, hp.1, inc n m s t e hs ht p hp.2⟩) hy
    · exact hsn.1.2 i x y hx (hy.elim fun p hp => ⟨p, hp.1, inc m n t s e ht hs p hp.2⟩)
  let ξ : BinarySchema 3 := { body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 4)
    (.conj (rd_entry0_m (.bound 1) .newest (.bound 6)) (rd_entry0_m (.bound 3) (.bound 2) .newest))) }
  have value i x : ξ.denote ρ i x ↔ ∃ n, M.mem n ω ∧ ∃ s, M.mem s T ∧ Rd_entry_d n s G ∧ Rd_entry_d i x s := by
    simp only [ξ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨g, hgX, hg, val⟩ := sc_uniform_source_l hZF hω source.transitive hc source.theory ξ
    (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
    ρ (Fin.cases source.omega_mem (Fin.cases hT (fun _ => hGX))) source.omega_mem hA (fun i hi => by
      obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
      obtain ⟨p, hp, hpn, _⟩ := path j hjω
      obtain ⟨x, hx, hix⟩ := hpn.2.2 i hj.predecessor_mem
      obtain ⟨_, n, hn, s, hs, hns, hps⟩ := (read p).mp hp
      exact ⟨x, hx, (value i x).mpr
        ⟨n, hn, s, hs, hns, hix.elim fun p hp => ⟨p, hp.1, hps p hp.2⟩⟩⟩)
  have gfn := fn0_function_l (ZF.modelsKP hZF) hg
  refine ⟨g, hgX, gfn, (Descriptive.tree_branch_l I hZF hω hJ gfn).mpr ?_⟩
  intro n hn
  obtain ⟨p, hp, hpn, _⟩ := path n hn
  refine ⟨p, sub p hp, (ds_restrict_iff_l I hpn gfn.1).mpr ?_⟩
  intro r hr
  obtain ⟨i, x, hir⟩ := hpn.1.1 r hr
  have hip : Rd_entry_d i x p := ⟨r, hir, hr⟩
  have hiω := hω.transitive (ZF.modelsKP hZF) n hn i (hpn.input_mem_of_pairMember hip)
  obtain ⟨y, _, hiy⟩ := hg.2.1 i hiω
  obtain ⟨m, _, t, _, hmt, hty⟩ := (value i y).mp (val i y hiy)
  obtain ⟨_, l, _, s, _, hls, hps⟩ := (read p).mp hp
  have eq := unique i l m s t x y hls hmt ⟨r, hir, hps r hr⟩ hty
  obtain ⟨v, hv, hvg⟩ := eq.symm ▸ hiy
  exact (kpair_unique_l M hZF.1 hv hir) ▸ hvg

end YesMetaZFC.SetTheory.LargeCardinal
