import YesMetaZFC.SetTheory.InnerModel.ProofCode.Order.Table

/-! # 有界构造树的实际内部语法检查器

P_T(n) 在 T 内收取所有叶码，以及子码已进入某个 P_T(m)、m∈n 的运算码。
检查器只检查语法，不调用 J 求值。每一步都是 Δ₀ 分离，递归算子对任意输入图总定义。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pg_gen_d (T V c : M.Domain) : Prop :=
  (∃ a, M.mem a T ∧ Pc_leaf_d T c a ∧ M.IsOrdinal a) ∨
    ∃ k a, M.mem a T ∧ ∃ b, M.mem b T ∧ ∃ d, M.mem d T ∧
      Pc_node_d T k c a b d ∧ M.mem a V ∧ M.mem b V ∧ M.mem d V

def pg_gen_m {n} (T V c : Term n) : Formula 1 n :=
  .disj (Formula.existsMem T (.conj (pc_leaf_m T.weaken c.weaken .newest) (KP.ord0_m .newest)))
    (rd_any_m rd_menu_l (fun k => Formula.existsMem T (Formula.existsMem T.weaken (Formula.existsMem T.weaken.weaken
      (.conj (pc_node_m T.weaken.weaken.weaken k c.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
        (.conj (.mem (.bound 2) V.weaken.weaken.weaken)
          (.conj (.mem (.bound 1) V.weaken.weaken.weaken) (.mem .newest V.weaken.weaken.weaken))))))))
derive_free_closed pg_gen_m
theorem pg_gen_delta_l {n} (T V c : Term n) : (pg_gen_m T V c).IsDelta0 :=
  .disj (.existsMem _ (.conj (pc_leaf_delta_l ..) (KP.ord0_delta_l _)))
    (rd_any_delta_l _ _ (fun _ => .existsMem _ (.existsMem _ (.existsMem _ (.conj (pc_node_delta_l ..)
      (.conj (.mem _ _) (.conj (.mem _ _) (.mem _ _))))))))
theorem pg_gen_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (T V c : Term n) :
    Formula.satisfies ρ (pg_gen_m T V c) ↔ Pg_gen_d (T.eval ρ) (V.eval ρ) (c.eval ρ) := by
  simp only [pg_gen_m, Pg_gen_d, Formula.satisfies_disj_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_conj_iff, pc_leaf_sat_l hKP.1, KP.ord0_sat_l hKP, rd_any_sat_l,
    pc_node_sat_l hKP.1, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact or_congr Iff.rfl ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, rd_menu_mem_l k, h⟩⟩

def Pg_slice_d (T V Y : M.Domain) : Prop := ∀ c, M.mem c Y ↔ M.mem c T ∧ Pg_gen_d T V c
def pg_slice_m {n} (T V Y : Term n) : Formula 1 n := .conj (Formula.subset Y T)
  (Formula.forallMem T (.iff (.mem .newest Y.weaken) (pg_gen_m T.weaken V.weaken .newest)))
derive_free_closed pg_slice_m
theorem pg_slice_delta_l {n} (T V Y : Term n) : (pg_slice_m T V Y).IsDelta0 :=
  .conj (.atom _ _ _) (.forallMem _ (.iff (.mem _ _) (pg_gen_delta_l ..)))
theorem pg_slice_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (T V Y : Term n) :
    Formula.satisfies ρ (pg_slice_m T V Y) ↔ Pg_slice_d (T.eval ρ) (V.eval ρ) (Y.eval ρ) := by
  simp only [pg_slice_m, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, pg_gen_sat_l hKP,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨hs, h⟩ c => ⟨fun hc => ⟨hs c hc, (h c (hs c hc)).mp hc⟩, fun hc => (h c hc.1).mpr hc.2⟩,
    fun h => ⟨fun c hc => ((h c).mp hc).1, fun c hc => (h c).trans ⟨And.right, fun hg => ⟨hc, hg⟩⟩⟩⟩

def pg_op_s : S1_binary 1 where
  -- 先取 R=ran(F)、V=⋃R，再从 T 中分离满足一步语法规则的码。
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj (rd_graph_m .range (.bound 4) (.bound 4) (.bound 4) (.bound 1))
        (.conj (rd_graph_m .union (.bound 1) (.bound 1) (.bound 1) .newest) (pg_slice_m (.bound 5) .newest (.bound 3)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (rd_graph_delta_l ..) (.conj (rd_graph_delta_l ..) (pg_slice_delta_l ..)))) }

theorem pg_op_sat_l (hKP : M.Models KP) (T F Y : M.Domain) :
    pg_op_s.schema.denote (rd_seed_env_l T) F Y ↔
      ∃ R V, Rd_fun_d .range F F F R ∧ Rd_fun_d .union R R R V ∧ Pg_slice_d T V Y := by
  rw [S1_binary.sat_l]
  simp only [pg_op_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_graph_sat_l hKP, pg_slice_sat_l hKP]
  change (∃ K R, M.mem R K ∧ ∃ V, M.mem V K ∧ _) ↔ _
  refine ⟨fun ⟨_, R, _, V, _, hr, hv, hy⟩ => ⟨R, V, hr, hv, hy⟩, ?_⟩
  rintro ⟨R, V, hr, hv, hy⟩
  obtain ⟨K, hk⟩ := KP.exists_pair hKP R V
  exact ⟨K, R, (hk R).mpr (Or.inl rfl), V, (hk V).mpr (Or.inr rfl), hr, hv, hy⟩

theorem pg_op_total_l (hKP : M.Models KP) (T F : M.Domain) : ∃ Y, pg_op_s.schema.denote (rd_seed_env_l T) F Y := by
  obtain ⟨R, hr⟩ := rd_fun_exists_l hKP .range F F F
  obtain ⟨V, hv⟩ := rd_fun_exists_l hKP .union R R R
  let φ : Delta0UnarySchema 2 := { body := pg_gen_m (.bound 2) (.bound 1) .newest, delta0 := pg_gen_delta_l .. }
  let ρ := (rd_seed_env_l T).push V
  obtain ⟨Y, hy⟩ := KP.separation_exists_d hKP φ ρ T
  exact ⟨Y, (pg_op_sat_l hKP T F Y).mpr ⟨R, V, hr, hv,
    fun c => (hy c).trans (and_congr_right fun _ => pg_gen_sat_l hKP _ _ _ _)⟩⟩

theorem pg_op_unique_l (hKP : M.Models KP) (T F Y Z : M.Domain)
    (hy : pg_op_s.schema.denote (rd_seed_env_l T) F Y) (hz : pg_op_s.schema.denote (rd_seed_env_l T) F Z) : Y = Z := by
  obtain ⟨R, V, hr, hv, hy⟩ := (pg_op_sat_l hKP T F Y).mp hy
  obtain ⟨S, W, hs, hw, hz⟩ := (pg_op_sat_l hKP T F Z).mp hz
  have he := rd_fun_unique_l hKP.1 hr hs; subst S
  have he := rd_fun_unique_l hKP.1 hv hw; subst W
  exact hKP.1.eq_of_same_members Y Z (fun c => (hy c).trans (hz c).symm)

def Pg_level_d (T n Y : M.Domain) : Prop := Rc_value_d pg_op_s (rd_seed_env_l T) n Y
def pg_level_m {n} (T h Y : Term n) : Formula 1 n := binary_pred_m (rc_value_s pg_op_s).schema (fun _ => T) h Y
derive_free_closed pg_level_m
theorem pg_level_sat_l (hE : Extensional M) {n} (ρ : Env M n) (T h Y : Term n) :
    Formula.satisfies ρ (pg_level_m T h Y) ↔ Pg_level_d (T.eval ρ) (h.eval ρ) (Y.eval ρ) := by
  rw [pg_level_m, binary_pred_sat_l]
  apply Iff.trans ?_ (rc_value_sat_l hE pg_op_s (rd_seed_env_l (T.eval ρ)) (h.eval ρ) (Y.eval ρ))
  exact Formula.closed_env_l _ (rc_value_s pg_op_s).schema.freeClosed rfl

theorem pg_level_exists_l (hM : M.Models KPi) (T n : M.Domain) : ∃ Y, Pg_level_d T n Y :=
  rc_value_exists_l hM _ _ (pg_op_total_l (KPi.models_iff_l.mp hM).1 T) (pg_op_unique_l (KPi.models_iff_l.mp hM).1 T) n
theorem pg_level_unique_l (hM : M.Models KPi) {T n Y Z : M.Domain} (hy : Pg_level_d T n Y) (hz : Pg_level_d T n Z) : Y = Z :=
  rc_value_unique_l hM _ _ (pg_op_unique_l (KPi.models_iff_l.mp hM).1 T) hy hz

theorem pg_level_equation_l (hM : M.Models KPi) {T n Y : M.Domain} (hy : Pg_level_d T n Y) :
    ∃ V, Pg_slice_d T V Y ∧ ∀ c, M.mem c V ↔ ∃ m, M.mem m n ∧ ∃ Z, Pg_level_d T m Z ∧ M.mem c Z := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨G, _, hop, hg⟩ := rc_value_equation_l hM pg_op_s (rd_seed_env_l T) (pg_op_unique_l hKP T) hy
  obtain ⟨R, V, hr, hv, hy⟩ := (pg_op_sat_l hKP T G Y).mp hop
  refine ⟨V, hy, fun c => ?_⟩
  rw [hv c]
  change (∃ Z, M.mem Z R ∧ M.mem c Z) ↔ _
  exact ⟨fun ⟨Z, hz, hc⟩ => ((hr Z).mp hz).elim (fun m hm => ⟨m, ((hg m Z).mp hm).1, Z, ((hg m Z).mp hm).2, hc⟩),
    fun ⟨m, hm, Z, hz, hc⟩ => ⟨Z, (hr Z).mpr ⟨m, (hg m Z).mpr ⟨hm, hz⟩⟩, hc⟩⟩

end YesMetaZFC.SetTheory.InnerModel
