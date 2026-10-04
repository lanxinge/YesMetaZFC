import YesMetaZFC.SetTheory.LargeCardinal.JointFiber
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullProjection

/-! # 有限支撑代表的函数空间与拉回方程

代表始终是指定源集合中的真实函数图。坐标拉回用逐值方程表达，因而不依赖
中间函数空间、投影图或商模型的编码选择。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_space_d (κ n D : M.Domain) : Prop := ∀ s, M.mem s D ↔ Fn0_d n κ s
def ep_space_m {d} (κ n D : Term d) : Formula 1 d := .forallE
  (.iff (.mem .newest D.weaken) (fn0_m n.weaken κ.weaken .newest))
derive_free_closed ep_space_m
theorem ep_space_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ n D : Term d) :
    Formula.satisfies ρ (ep_space_m κ n D) ↔ Ep_space_d (κ.eval ρ) (n.eval ρ) (D.eval ρ) := by
  simp only [ep_space_m, Ep_space_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def Ep_fun_d (κ X n f : M.Domain) : Prop := ∃ D, Ep_space_d κ n D ∧ Fn0_d D X f
def ep_fun_m {d} (κ X n f : Term d) : Formula 1 d := .existsE
  (.conj (ep_space_m κ.weaken n.weaken .newest) (fn0_m .newest X.weaken f.weaken))
derive_free_closed ep_fun_m
theorem ep_fun_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ X n f : Term d) :
    Formula.satisfies ρ (ep_fun_m κ X n f) ↔ Ep_fun_d (κ.eval ρ) (X.eval ρ) (n.eval ρ) (f.eval ρ) := by
  simp only [ep_fun_m, Ep_fun_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ep_space_sat_l hE, fn0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem Ep_fun_d.at_l (hE : Extensional M) {κ X n f D : M.Domain}
    (hf : Ep_fun_d κ X n f) (hD : Ep_space_d κ n D) : Fn0_d D X f := by
  obtain ⟨E, hE', hf⟩ := hf
  exact hE.eq_of_same_members E D (fun s => (hE' s).trans (hD s).symm) ▸ hf

def Ep_pull_d (κ X m n q f g : M.Domain) : Prop := Ep_fun_d κ X m f ∧ Ep_fun_d κ X n g ∧
  ∀ s r, Fn0_d n κ s → Cp0_d m n κ q s r → ∀ x, Rd_entry_d s x g ↔ Rd_entry_d r x f

def ep_pull_m {d} (κ X m n q f g : Term d) : Formula 1 d := .conj (ep_fun_m κ X m f)
  (.conj (ep_fun_m κ X n g) (.forallE (.forallE (.imp (fn0_m n.weaken.weaken κ.weaken.weaken (.bound 1))
    (.imp (cp0_m m.weaken.weaken n.weaken.weaken κ.weaken.weaken q.weaken.weaken (.bound 1) .newest)
      (.forallE (.iff (rd_entry_m (.bound 2) .newest g.weaken.weaken.weaken)
        (rd_entry_m (.bound 1) .newest f.weaken.weaken.weaken))))))))
derive_free_closed ep_pull_m
theorem ep_pull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ X m n q f g : Term d) :
    Formula.satisfies ρ (ep_pull_m κ X m n q f g) ↔
      Ep_pull_d (κ.eval ρ) (X.eval ρ) (m.eval ρ) (n.eval ρ) (q.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [ep_pull_m, Ep_pull_d, Formula.satisfies_conj_iff, ep_fun_sat_l hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, fn0_sat_l hE, cp0_sat_l hE,
    Formula.satisfies_iff_iff, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ep_pull_of_comp_l {κ X m n q D E t f g : M.Domain}
    (hD : Ep_space_d κ m D) (hE' : Ep_space_d κ n E) (ht : Fn0_d E D t) (hf : Fn0_d D X f)
    (spec : ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r)
    (h : Cp0_d E D X t f g) : Ep_pull_d κ X m n q f g :=
  ⟨⟨D, hD, hf⟩, ⟨E, hE', h.1⟩, fun s r hs hr _ => h.value_l ht hf ((spec s r).mpr ⟨(hE' s).mpr hs, hr⟩)⟩

theorem ep_pull_comp_l (hKP : M.Models KP) {κ X m n l q r t f g h : M.Domain}
    (hq : Fn0_d m n q) (hr : Fn0_d n l r) (ht : Cp0_d m n l q r t)
    (hfg : Ep_pull_d κ X m n q f g) (hgh : Ep_pull_d κ X n l r g h) : Ep_pull_d κ X m l t f h := by
  refine ⟨hfg.1, hgh.2.1, fun s u hs hu x => ?_⟩
  obtain ⟨v, hv⟩ := cp0_exists_l hKP hr hs
  obtain ⟨w, hw⟩ := cp0_exists_l hKP hq hv.1
  have e := cp0_unique_l hKP.1 ht.1 hs (Cp0_d.assoc_l hr hq ht hs hv hw) hu
  subst w
  exact (hgh.2.2 s v hs hv x).trans (hfg.2.2 v u hv.1 hw x)

theorem ep_pull_id_l (hE : Extensional M) {κ X n q f : M.Domain} (hf : Ep_fun_d κ X n f)
    (idq : ∀ i j, Rd_entry_d i j q → i = j) : Ep_pull_d κ X n n q f f := by
  refine ⟨hf, hf, fun s r hs hr x => ?_⟩
  have e : r = s := hr.1.ext_l hE hs fun i hi => by
    obtain ⟨j, _, y, _, hij, hjy, hiy⟩ := hr.2 i hi
    exact ⟨y, hiy, (idq i j hij).symm ▸ hjy⟩
  exact e ▸ Iff.rfl

theorem ep_pull_unique_l (hKP : M.Models KP) {κ X m n q f g h : M.Domain} (hq : Fn0_d m n q)
    (hg : Ep_pull_d κ X m n q f g) (hh : Ep_pull_d κ X m n q f h) : g = h := by
  obtain ⟨E, he, hge⟩ := hg.2.1
  have hhe := hh.2.1.at_l hKP.1 he
  apply hge.ext_l hKP.1 hhe
  intro s hs
  obtain ⟨r, hr⟩ := cp0_exists_l hKP hq ((he s).mp hs)
  obtain ⟨x, _, hsx⟩ := hge.2.1 s hs
  exact ⟨x, hsx, (hh.2.2 s r ((he s).mp hs) hr x).mpr ((hg.2.2 s r ((he s).mp hs) hr x).mp hsx)⟩

end YesMetaZFC.SetTheory.LargeCardinal
