import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 原关系模型中的完整记录与元组

背景只保存载体、关系和对象码。全部坐标先检查所属，再在原关系结构中
解释原公式；元组的配对也是该结构的配对。高层记录不经过共同低层实现。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

abbrev Rf_record_d {n} (X R : M.Domain) (φ : Formula 1 (n+1)) (C r : M.Domain) : Prop :=
  Rr_truth_d I X R (rt_record_in0_m φ) (Fin.cases C (fun _ => r))

abbrev Rf_tuple_d {n} (X R : M.Domain) (v : Fin (n+1) → M.Domain) (r : M.Domain) : Prop :=
  Rr_truth_d I X R (rt_tuple_m (fun i : Fin (n+1) => .bound i.succ) .newest) (Fin.cases r v)

def rf_record_m {d n} (φ : Formula 1 (n+1)) (X R C r : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := 𝒞) (rt_record_in0_m φ) X R (Fin.cases C (fun _ => r))

def rf_tuple_m {d n} (X R : Term d) (v : Fin (n+1) → Term d) (r : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := 𝒞) (rt_tuple_m (fun i : Fin (n+1) => .bound i.succ) .newest) X R (Fin.cases r v)

@[simp] theorem rf_record_closed_l {d n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (X R C r : Term d) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hC : C.freeSupport = []) (hr : r.freeSupport = []) : (rf_record_m (𝒞 := 𝒞) φ X R C r).FreeClosed :=
  rr_truth_closed_l _ (rt_record_in0_closed_l φ closed) X R _ hX hR (Fin.cases hC (fun _ => hr))

@[simp] theorem rf_tuple_closed_l {d n} (X R : Term d) (v : Fin (n+1) → Term d) (r : Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hv : ∀ i, (v i).freeSupport = [])
    (hr : r.freeSupport = []) : (rf_tuple_m (𝒞 := 𝒞) X R v r).FreeClosed :=
  rr_truth_closed_l _ (rt_tuple_closed_l _ _ (fun _ => rfl) rfl) X R _ hX hR (Fin.cases hr hv)

theorem rf_record_sat_l {d n} (ρ : Env M d) (φ : Formula 1 (n+1)) (closed : φ.FreeClosed) (X R C r : Term d) :
    Formula.satisfies ρ (rf_record_m (𝒞 := 𝒞) φ X R C r) ↔
      Rf_record_d I (X.eval ρ) (R.eval ρ) φ (C.eval ρ) (r.eval ρ) := by
  rw [rf_record_m, rr_truth_sat_l I ρ _ (rt_record_in0_closed_l φ closed)]
  have eq : (fun i : Fin 2 => ((Fin.cases C (fun _ => r) : Fin 2 → Term d) i).eval ρ) =
      Fin.cases (C.eval ρ) (fun _ => r.eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  rw [eq]

theorem rf_tuple_sat_l {d n} (ρ : Env M d) (X R : Term d) (v : Fin (n+1) → Term d) (r : Term d) :
    Formula.satisfies ρ (rf_tuple_m (𝒞 := 𝒞) X R v r) ↔
      Rf_tuple_d I (X.eval ρ) (R.eval ρ) (fun i => (v i).eval ρ) (r.eval ρ) := by
  rw [rf_tuple_m, rr_truth_sat_l I ρ _ (rt_tuple_closed_l _ _ (fun _ => rfl) rfl)]
  have eq : (fun i : Fin (n+2) => ((Fin.cases r v : Fin (n+2) → Term d) i).eval ρ) =
      Fin.cases (r.eval ρ) (fun i => (v i).eval ρ) := funext (Fin.cases rfl (fun _ => rfl))
  rw [eq]

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系对象的有序对

成员守卫与配对公式统一在原模型中解释；背景只处理对象码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

abbrev Rf_pair_d (X R u a b : M.Domain) : Prop :=
  Rr_truth_d I (n := 2) X R (kpair0_m .newest (.bound 1) (.bound 2)) (Fin.cases u (Fin.cases a (fun _ => b)))

def rf_pair_m {d} (X R u a b : Term d) : Formula 1 d :=
  rr_truth_m (𝒞 := 𝒞) (n := 2) (kpair0_m .newest (.bound 1) (.bound 2)) X R (Fin.cases u (Fin.cases a (fun _ => b)))

@[simp] theorem rf_pair_closed_l {d} (X R u a b : Term d) (hX : X.freeSupport = [])
    (hR : R.freeSupport = []) (hu : u.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (rf_pair_m (𝒞 := 𝒞) X R u a b).FreeClosed :=
  rr_truth_closed_l _ (by simp -implicitDefEqProofs) X R _ hX hR (Fin.cases hu (Fin.cases ha (fun _ => hb)))

theorem rf_pair_sat_l {d} (ρ : Env M d) (X R u a b : Term d) :
    Formula.satisfies ρ (rf_pair_m (𝒞 := 𝒞) X R u a b) ↔
      Rf_pair_d I (X.eval ρ) (R.eval ρ) (u.eval ρ) (a.eval ρ) (b.eval ρ) := by
  rw [rf_pair_m, rr_truth_sat_l I ρ _ (by simp -implicitDefEqProofs)]
  have eq : (fun i : Fin 3 => ((Fin.cases u (Fin.cases a (fun _ => b)) : Fin 3 → Term d) i).eval ρ) =
      Fin.cases (u.eval ρ) (Fin.cases (a.eval ρ) (fun _ => b.eval ρ)) :=
    funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
  rw [eq]

theorem Rf_pair_d.bounds_l {X R u a b} (h : Rf_pair_d I X R u a b) :
    M.mem u X ∧ M.mem a X ∧ M.mem b X :=
  h.elim fun bound _ => ⟨bound 0, bound 1, bound 2⟩

theorem rf_pair_native_l {X R} (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (u a b : (smdl_structure_l I (R := R) nx).Domain) :
    Rf_pair_d I X R u.val a.val b.val ↔ KPair_d (smdl_structure_l I (R := R) nx) u a b := by
  exact ⟨fun ⟨_, h⟩ => (kpair0_sat_l ext ..).mp h,
    fun h => ⟨Fin.cases u.property (Fin.cases a.property (fun _ => b.property)), (kpair0_sat_l ext ..).mpr h⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系反射层中的记录读写

反射层的传递性只在原结构内解释。坐标、配对见证及新记录都留在该结构，
既不把对象码解释成背景集合，也不要求整个源或目标在背景中良基。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
  {X R : M.Domain} (nx : ∃ x, M.mem x X)
local notation "N" => smdl_structure_l I (R := R) nx

theorem rf_record_native_l {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (C r : (N).Domain) : Rf_record_d I X R φ C.val r.val ↔ Rt_record_in_d φ C r := by
  have eq : (fun i : Fin 2 => ((Fin.cases C (fun _ => r) : Fin 2 → (N).Domain) i).val) =
      Fin.cases C.val (fun _ => r.val) := funext (Fin.cases rfl (fun _ => rfl))
  have read := rr_truth_native_l I nx (rt_record_in0_m φ) (rt_record_in0_closed_l φ closed)
    (Fin.cases C (fun _ => r))
  rw [eq] at read
  exact read

theorem rf_tuple_native_l (ext : Extensional N) {n} (v : Fin (n+1) → (N).Domain) (r : (N).Domain) :
    Rf_tuple_d I X R (fun i => (v i).val) r.val ↔ Rt_tuple_d v r := by
  let ρ : Env N (n+2) := ⟨Fin.cases r v, fun _ => r⟩
  have eq : (fun i : Fin (n+2) => (ρ.bound i).val) = Fin.cases r.val (fun i => (v i).val) :=
    funext (Fin.cases rfl (fun _ => rfl))
  have read := (rr_truth_native_l I nx _ (rt_tuple_closed_l _ _ (fun _ => rfl) rfl) ρ.bound).trans
    (rt_tuple_sat_l ext ρ (fun i => .bound i.succ) .newest)
  rw [eq] at read
  exact read

omit nx in
/-- 同一原关系记录的坐标唯一；不对对象码使用背景中的配对单值性。 -/
theorem Rf_tuple_d.inj_l {n} {v w : Fin (n+1) → M.Domain} {r : M.Domain}
    (ext : Rf_ext_d I X R) (a : Rf_tuple_d I X R v r) (b : Rf_tuple_d I X R w r) : v = w := by
  have av := a.elim fun m _ => m
  have bv := b.elim fun m _ => m
  let nx : ∃ x, M.mem x X := ⟨r, av 0⟩
  let N₀ := smdl_structure_l I (R := R) nx
  let f : Fin (n+1) → N₀.Domain := fun i => ⟨v i, av i.succ⟩
  let g : Fin (n+1) → N₀.Domain := fun i => ⟨w i, bv i.succ⟩
  have eq := rt_tuple_inj_l
    ((rf_tuple_native_l I nx (ext.native_l I nx) f ⟨r, av 0⟩).mp a)
    ((rf_tuple_native_l I nx (ext.native_l I nx) g ⟨r, av 0⟩).mp b)
  exact funext fun i => congrArg Subtype.val (congrFun eq i)

/-- 全部量词在原反射层中读取；返回的元组仍是同一原关系中的记录。 -/
theorem rf_record_read_l (ext : Extensional N) {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (C r : (N).Domain) (trans : (N).TransitiveSet C)
    (nc : Nonempty {x : (N).Domain // (N).mem x C}) : Rf_record_d I X R φ C.val r.val ↔
      (N).mem r C ∧ ∃ ρ : Env (rt_model_l C nc) (n+1),
        Rf_tuple_d I X R (fun i => (ρ.bound i).val.val) r.val ∧ Formula.satisfies ρ φ := by
  rw [rf_record_native_l I nx φ closed C r, rt_record_in_read_l ext φ closed trans nc]
  constructor
  · rintro ⟨hr, v, tuple, valid⟩
    exact ⟨hr, ⟨v, fun _ => v 0⟩, (rf_tuple_native_l I nx ext _ r).mpr tuple, valid⟩
  · rintro ⟨hr, ρ, tuple, valid⟩
    exact ⟨hr, ρ.bound, (rf_tuple_native_l I nx ext _ r).mp tuple,
      (Formula.closed_env_l φ closed (ρ := ρ) (η := ⟨ρ.bound, fun _ => ρ.bound 0⟩) rfl).mp valid⟩

/-- 有限配对在原反射层内产生实际记录码，完整原公式随之保存。 -/
theorem rf_record_save_l (ext : Extensional N) {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (C : (N).Domain) (trans : (N).TransitiveSet C)
    (pair : ∀ a b, (N).mem a C → (N).mem b C → ∃ p, (N).mem p C ∧ Pair_d N p a b)
    (nc : Nonempty {x : (N).Domain // (N).mem x C}) (ρ : Env (rt_model_l C nc) (n+1))
    (valid : Formula.satisfies ρ φ) : ∃ r : (N).Domain,
      Rf_record_d I X R φ C.val r.val ∧ Rf_tuple_d I X R (fun i => (ρ.bound i).val.val) r.val := by
  obtain ⟨r, record, tuple⟩ := rt_record_in_save_l ext φ closed trans pair nc ρ valid
  exact ⟨r, (rf_record_native_l I nx φ closed C r).mpr record,
    (rf_tuple_native_l I nx ext _ r).mpr tuple⟩

/-- 已保存的完整坐标由原关系配对的单值性恢复，不要求对象码之间的背景配对。 -/
theorem Rf_record_d.values_l (ext : Extensional N) {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed)
    (C r : (N).Domain) (trans : (N).TransitiveSet C)
    (nc : Nonempty {x : (N).Domain // (N).mem x C})
    {v : Fin (n+1) → M.Domain} (record : Rf_record_d I X R φ C.val r.val)
    (tuple : Rf_tuple_d I X R v r.val) : ∃ ρ : Env (rt_model_l C nc) (n+1),
      (∀ i, (ρ.bound i).val.val = v i) ∧ Formula.satisfies ρ φ := by
  obtain ⟨_, ρ, saved, valid⟩ := (rf_record_read_l I nx ext φ closed C r trans nc).mp record
  have hv := tuple.elim fun mem _ => fun i : Fin (n+1) => mem i.succ
  let w : Fin (n+1) → (N).Domain := fun i => ⟨v i, hv i⟩
  have eq := rt_tuple_inj_l ((rf_tuple_native_l I nx ext _ r).mp saved)
    ((rf_tuple_native_l I nx ext w r).mp tuple)
  exact ⟨ρ, fun i => congrArg (fun x : (N).Domain => x.val) (congrFun eq i), valid⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 原关系初等边上的完整记录恢复

先搬运完整记录和坐标公式，再在目标自己的反射层中解码。目标层的成员
可以有新参数；完整原公式的真值由原初等图保证，不限制到旧参数的像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Smap_d.record_image_l (hZF : M.Models ZF) {ω c d X R Y S j C r : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (map : Smap_d I ω c d X Y j) (ext : Extensional (smdl_structure_l I (R := S) my.2.1))
    (D : (smdl_structure_l I (R := S) my.2.1).Domain) (image : M.PairMember I C D.val j)
    (trans : (smdl_structure_l I (R := S) my.2.1).TransitiveSet D)
    (nd : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x D})
    {n} (φ : Formula 1 (n+1)) (closed : φ.FreeClosed) {v : Fin (n+1) → M.Domain}
    (record : Rf_record_d I X R φ C r) (tuple : Rf_tuple_d I X R v r) :
    ∃ s : (smdl_structure_l I (R := S) my.2.1).Domain, ∃ ρ : Env (rt_model_l D nd) (n+1),
      M.PairMember I r s.val j ∧ (∀ i, M.PairMember I (v i) (ρ.bound i).val.val j) ∧
      Rf_record_d I Y S φ D.val s.val ∧ Rf_tuple_d I Y S (fun i => (ρ.bound i).val.val) s.val ∧
      Formula.satisfies ρ φ := by
  obtain ⟨s, hs, hrs⟩ := map.1.1.2.2 r (record.elim fun mem _ => mem 1)
  have saved : Rf_record_d I Y S φ D.val s := record.map_l I hZF hω mx my map
    (rt_record_in0_closed_l φ closed) (Fin.cases image (fun _ => hrs))
  have values (i : Fin (n+1)) : ∃ w, M.PairMember I (v i) w j := by
    obtain ⟨w, _, hw⟩ := map.1.1.2.2 (v i) (tuple.elim fun mem _ => mem i.succ)
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice values
  have copied : Rf_tuple_d I Y S w s := tuple.map_l I hZF hω mx my map
    (rt_tuple_closed_l _ _ (fun _ => rfl) rfl) (Fin.cases hrs hw)
  obtain ⟨ρ, eq, valid⟩ := saved.values_l I my.2.1 ext φ closed D ⟨s, hs⟩ trans nd copied
  have bound : (fun i => (ρ.bound i).val.val) = w := funext eq
  exact ⟨⟨s, hs⟩, ρ, hrs, fun i => (eq i).symm ▸ hw i, saved, bound.symm ▸ copied, valid⟩

end YesMetaZFC.SetTheory.Internal
