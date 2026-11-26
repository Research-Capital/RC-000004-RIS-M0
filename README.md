# RC-000004-RIS-M₀ — Hai phép affine chia đôi simplex

**Tác giả bài báo** Dr.rer.nat DUYMT  
**Bản thảo** *Hai phép co affine cho simplex n chiều*, RC-000004-IFS-SIMPLEX  
**Kết quả được chọn** Phân hoạch và tính bất biến trong Bổ đề 2.1 và 2.3.

## Phát biểu

Trong chiều $d$, đặt $S=\{x\in\mathbb R^d:x_j\ge0,\ \sum_j x_j\le1\}$
và $\ell(x)=x_1+\sum_j x_j$. Hai công thức trong bài là

$$
F_0(x)=(x_d/2,x_1,\ldots,x_{d-1}),\qquad
F_1(x)=(x_d/2+1-\textstyle\sum_j x_j,x_1,\ldots,x_{d-1}).
$$

| Định lý Lean trong [Simplex.lean](Simplex.lean) | Nội dung |
|---|---|
| `image_eq_half` | $F_0(S)=S\cap\{\ell\le1\}$ và $F_1(S)=S\cap\{\ell\ge1\}$. |
| `image_union` | $F_0(S)\cup F_1(S)=S$. |
| `image_inter` | $F_0(S)\cap F_1(S)=S\cap\{\ell=1\}$. |

Lean dùng chỉ số bắt đầu từ 0 và viết $d=n+1$. Chứng minh áp dụng cho
mọi $d\ge1$, gồm tam giác ($d=2$) và tứ diện ($d=3$).
Phạm vi kiểm chứng là các đẳng thức tập hợp ở trên. Tính co trong chuẩn
thích nghi, tính duy nhất của attractor và các kết quả phổ của bài báo
nằm ngoài phạm vi bản hình thức hóa này.

## Ý tưởng chứng minh

Viết điểm đích dưới dạng $(a,u)$, với $a$ là tọa độ đầu và $u$ là
các tọa độ còn lại. Trong nửa dưới, tiền ảnh được chọn là $(u,2a)$.
Trong nửa trên, tiền ảnh được chọn là $(u,2(1-a-\sum u))$.
Các bất đẳng thức xác định nửa simplex bảo đảm mỗi tiền ảnh có tọa độ
không âm và tổng không vượt quá 1. Theo chiều thuận, tách tọa độ cuối
của điểm nguồn cho các bất đẳng thức tương ứng tại điểm ảnh.
Hai đẳng thức cuối suy ra từ thứ tự tuyến tính của số thực.

## Tái lập kiểm chứng

Cài [Lean qua Elan](https://lean-lang.org/install/), rồi chạy trong thư mục kho:

    lake exe cache get Mathlib/Algebra/BigOperators/Fin.lean Mathlib/Data/Real/Basic.lean Mathlib/Tactic/Linarith.lean
    lake build
    lake env lean -DwarningAsError=true Simplex.lean

`lean-toolchain` ghim Lean 4.24.0. `lakefile.toml` ghim commit mathlib.
Ba lệnh `#print axioms` cuối mã in các tiên đề mà chứng minh phụ thuộc.
Kết quả kiểm tra chỉ gồm `propext`, `Classical.choice` và `Quot.sound`.
