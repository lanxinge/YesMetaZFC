import YesMetaZFC.Model.SetTheory.Internal.SourceCollapse
import YesMetaZFC.Model.SetTheory.Internal.SourceFamily

/-! # 源内小关系的传递像及求值图

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
    (theory : Sc_theory_d I ω X R) (collapse : Sc_collapse_d X)
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
  obtain ⟨B', g', hB', hg', iso'⟩ := collapse.collapse_l hC hS small' (iso.well_founded_l (ZF.modelsKP hZF)) (iso.extensional_l hZF.1)
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
