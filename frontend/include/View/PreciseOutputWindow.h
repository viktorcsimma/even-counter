#ifndef PRECISEOUTPUTWINDOW_H
#define PRECISEOUTPUTWINDOW_H

#include <QDialog>

#include "ViewModel/PreciseOutputViewModel.hpp"

QT_BEGIN_NAMESPACE
namespace Ui {
class PreciseOutputWindow;
}
QT_END_NAMESPACE

// A window presenting the result with an arbitrarily long precision
// in a large text area.
// Constructs the view model (PreciseOutputViewModel) by itself
// and does _not_ free the HsCalcStateWrapper instance on destruction.
// Runs calculations asynchronously.
class PreciseOutputWindow: public QDialog {
    Q_OBJECT

public:
    // Takes a reference to a given view model
    // and displays the same result with the same precision
    // as the main window so as to avoid an immediate recalculation.
    // The parent should be the main window.
    // Beware: the reference must remain valid throughout the existence of the window.
    PreciseOutputWindow(PreciseOutputViewModel& viewModel, QWidget* parent = nullptr);

    // Also cancels the current calculation, if any.
    ~PreciseOutputWindow();

public slots:
    // Runs when the graphical button is clicked
    // but _not_ when the physical Enter button is used.
    // Starts a new calculation or cancels the current one, if there is one.
    void evaluateButtonClicked();
    // Runs when the physical Enter button is pressed.
    // Starts a calculation if there is none; does nothing otherwise.
    void enterKeyPressed();

private:
    Ui::PreciseOutputWindow *ui;

    PreciseOutputViewModel& viewModel;

    // Starts the calculation.
    // Beware: only use this if there is no calculation in progress!
    void startEvaluation();
    // Cancels the calculation if there is one;
    // does nothing otherwise.
    void interruptEvaluation();

private slots:
    // Called by the evaluationFinished() signal.
    // The signal-slot mechanism ensures
    // that this always runs on the main thread.
    void onEvaluationFinished();

signals:
    // Emitted by the calculation thread
    // when it finishes.
    void evaluationFinished();
};

#endif // PRECISEOUTPUTWINDOW_H
