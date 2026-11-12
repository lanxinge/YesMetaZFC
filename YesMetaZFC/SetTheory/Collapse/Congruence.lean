import YesMetaZFC.SetTheory.Collapse.Recursion

/-! # 坍塌核与成员同余

源成员结构不必外延。只要求有相同前驱的点在成员关系中可替换；
内部成员归纳便证明：两个点坍塌为同一集合，当且仅当它们有相同前驱。
该条件是一条原语言句子，传递见证自动满足它。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Mc_same_d (X a b : M.Domain) : Prop := ∀ z, M.mem z X → (M.mem z a ↔ M.mem z b)

def Mc_congr_d (X : M.Domain) : Prop := ∀ a, M.mem a X → ∀ b, M.mem b X →
  Mc_same_d X a b → ∀ z, M.mem z X → (M.mem a z ↔ M.mem b z)

def Mc_ext_d (X : M.Domain) : Prop := ∀ a, M.mem a X → ∀ b, M.mem b X → Mc_same_d X a b → a = b

theorem Mc_ext_d.congr_l {X : M.Domain} (h : Mc_ext_d X) : Mc_congr_d X :=
  fun a ha b hb eq _ _ => h a ha b hb eq ▸ Iff.rfl

theorem mc_transitive_ext_l (hE : Extensional M) {X : M.Domain} (ht : M.TransitiveSet X) : Mc_ext_d X := by
  intro a ha b hb eq
  exact hE.eq_of_same_members a b fun z =>
    ⟨fun hz => (eq z (ht a ha z hz)).mp hz, fun hz => (eq z (ht b hb z hz)).mpr hz⟩

def mc_same_m {n} (X a b : Term n) : Formula 1 n :=
  Formula.forallMem X (.iff (.mem .newest a.weaken) (.mem .newest b.weaken))
derive_free_closed mc_same_m

theorem mc_same_sat_l {n} (ρ : Env M n) (X a b : Term n) :
    Formula.satisfies ρ (mc_same_m X a b) ↔ Mc_same_d (X.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [mc_same_m,Mc_same_d,Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff,Definitional.Term.eval_weaken,Definitional.Term.eval_newest]

/-- 此句使用原语言的外延等同，不声称源的代表元具有字面唯一性。 -/
def mc_congr_m {n} : Formula 1 n := .forallE (.forallE
  (.imp (Formula.extensionalEq (.bound 1) .newest)
    (.forallE (.iff (.mem (.bound 2) .newest) (.mem (.bound 1) .newest)))))

theorem mc_congr_closed_l {n} : (mc_congr_m (n := n)).FreeClosed := by
  simp [mc_congr_m,Definitional.Formula.FreeClosed,Formula.extensionalEq]

theorem mc_congr_sat_l {n} (ρ : Env M n) : Formula.satisfies ρ mc_congr_m ↔
    ∀ a b, (∀ x, M.mem x a ↔ M.mem x b) → ∀ z, M.mem a z ↔ M.mem b z := by
  simp only [mc_congr_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_extensionalEq_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff]
  rfl

theorem mc_value_kernel_l (hM : M.Models KPi) {X a b y : M.Domain} (hc : Mc_congr_d X)
    (ha : M.mem a X) (hb : M.mem b X) (h : Mc_value_d X a y) (g : Mc_value_d X b y) : Mc_same_d X a b := by
  let hE := (KPi.models_iff_l.mp hM).1.1
  let φ : UnarySchema 1 := { body := (.forallE <| .forallE <| .imp (.mem (.bound 2) (.bound 3)) <|
    .imp (.mem (.bound 1) (.bound 3)) <| .imp (mc_value_m (.bound 3) (.bound 2) .newest) <|
      .imp (mc_value_m (.bound 3) (.bound 1) .newest) (mc_same_m (.bound 3) (.bound 2) (.bound 1))) }
  have sat a : φ.denote (mc_env_l X) a ↔
      ∀ b y, M.mem a X → M.mem b X → Mc_value_d X a y → Mc_value_d X b y → Mc_same_d X a b := by
    simp only [UnarySchema.denote,φ,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff,mc_value_sat_l hE,mc_same_sat_l]; rfl
  apply (sat a).mp ((KPi.models_iff_l.mp hM).2 φ (mc_env_l X) ?_ a) b y ha hb h g
  intro a ih
  apply (sat a).mpr
  intro b y ha hb h g z hz
  constructor
  · intro hza
    obtain ⟨v,hv⟩ := mc_value_exists_l hM X z
    obtain ⟨w,hwb,hw,hwv⟩ := (mc_value_equation_l hM g v).mp
      ((mc_value_equation_l hM h v).mpr ⟨z,hza,hz,hv⟩)
    exact (hc z hz w hw ((sat z).mp (ih z hza) w v hz hw hv hwv) b hb).mpr hwb
  · intro hzb
    obtain ⟨v,hv⟩ := mc_value_exists_l hM X z
    obtain ⟨w,hwa,hw,hwv⟩ := (mc_value_equation_l hM h v).mp
      ((mc_value_equation_l hM g v).mpr ⟨z,hzb,hz,hv⟩)
    exact (hc w hw z hz ((sat w).mp (ih w hwa) z v hw hz hwv hv) a ha).mp hwa

/-- 同前驱蕴含同坍塌值，不使用成员同余。 -/
theorem mc_value_same_l (hM : M.Models KPi) {X a b x y : M.Domain}
    (hs : Mc_same_d X a b) (h : Mc_value_d X a x) (g : Mc_value_d X b y) : x = y := by
  apply (KPi.models_iff_l.mp hM).1.1.eq_of_same_members
  intro z
  rw [mc_value_equation_l hM h z,mc_value_equation_l hM g z]
  exact ⟨fun ⟨t,ht,hX,hv⟩ => ⟨t,(hs t hX).mp ht,hX,hv⟩,
    fun ⟨t,ht,hX,hv⟩ => ⟨t,(hs t hX).mpr ht,hX,hv⟩⟩

end YesMetaZFC.SetTheory
